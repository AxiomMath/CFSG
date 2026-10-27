module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionThreeDefs
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81LThreeFourAutModel
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionLinear
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81LThreeFourAutGSp
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionAutomizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSectionThree

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

theorem exists_isPGroup_map_eq_and_lift {H L : Type*} [Group H] [Group L] [Finite H] {p : ℕ}
    [Fact p.Prime] (f : H →* L) (hf : Function.Surjective f) {E : Subgroup L}
    (hE : IsPGroup p E) :
    ∃ S : Subgroup H, IsPGroup p S ∧ S.map f = E ∧
      ∀ t ∈ Subgroup.normalizer (E : Set L), ∃ n ∈ Subgroup.normalizer (S : Set H), f n = t := by
  set M : Subgroup H := E.comap f with hM
  obtain ⟨Q⟩ : Nonempty (Sylow p M) := inferInstance
  set S : Subgroup H := (Q : Subgroup M).map M.subtype with hS
  have hSM : S ≤ M := Subgroup.map_subtype_le _
  have hSE : S.map f = E := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr hSM) fun e he => ?_
    let P : Sylow p E := Q.mapSurjective (f.subgroupComap_surjective E hf)
    have htop : (⊤ : Subgroup E) = P := P.is_maximal' (hE.to_subgroup ⊤) le_top
    have hmem : (⟨e, he⟩ : E) ∈ (P : Subgroup E) := htop ▸ Subgroup.mem_top _
    rw [Sylow.coe_mapSurjective] at hmem
    obtain ⟨x, hx, hxe⟩ := hmem
    exact ⟨x, ⟨x, hx, rfl⟩, congrArg Subtype.val hxe⟩
  refine ⟨S, Q.isPGroup'.map M.subtype, hSE, fun t ht => ?_⟩
  obtain ⟨h, rfl⟩ := hf t
  set S' : Subgroup H := S.map (MulAut.conj h⁻¹).toMonoidHom with hS'
  have hmemS' : ∀ x, x ∈ S' ↔ h * x * h⁻¹ ∈ S := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hy
    · intro hx
      exact ⟨h * x * h⁻¹, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hS'M : S' ≤ M := by
    intro x hx
    have h1 : f (h * x * h⁻¹) ∈ E := hSM ((hmemS' x).mp hx)
    rw [map_mul, map_mul, map_inv] at h1
    exact (Subgroup.mem_normalizer_iff.mp ht (f x)).mpr h1
  have hcard : Nat.card (S'.subgroupOf M) = p ^ (Nat.card M).factorization p := by
    calc Nat.card (S'.subgroupOf M) = Nat.card S' :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS'M).toEquiv
      _ = Nat.card S := Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective
      _ = Nat.card (Q : Subgroup M) := Subgroup.card_map_of_injective M.subtype_injective
      _ = _ := Sylow.card_eq_multiplicity Q
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq M Q (Sylow.ofCard (S'.subgroupOf M) hcard)
  have hcN : h * (c : H) ∈ Subgroup.normalizer (S : Set H) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 : c * y * c⁻¹ ∈ ((c • Q : Sylow p M) : Subgroup M) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj c) _ hy
    rw [hc, Sylow.coe_ofCard, Subgroup.mem_subgroupOf] at h1
    have h2 := (hmemS' _).mp h1
    have e : h * (c : H) * (y : H) * (h * (c : H))⁻¹ =
        h * ((c * y * c⁻¹ : M) : H) * h⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    change h * (c : H) * (y : H) * (h * (c : H))⁻¹ ∈ S
    rw [e]
    exact h2
  have hcE : f (c : H) ∈ S.map f := by
    rw [hSE]
    exact c.2
  obtain ⟨s, hs, hsc⟩ := hcE
  refine ⟨h * c * s⁻¹, Subgroup.mul_mem _ hcN (Subgroup.le_normalizer (S.inv_mem hs)), ?_⟩
  rw [map_mul, map_mul, map_inv, hsc, mul_inv_cancel_right]

theorem eq_of_map_eq_of_isPGroup {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {H L : Type*} [Group H] [Group L] (ρ : H →* L)
    (hρ : ∀ x : H, ρ x = 1 → ∃ k : ℕ, x ^ (q ^ k) = 1)
    {T : Subgroup H} (hT : IsPGroup p T) {x y : H} (hx : x ∈ T) (hy : y ∈ T)
    (hxy : ρ x = ρ y) : x = y := by
  have h1 : ρ (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  obtain ⟨k, hk⟩ := hρ _ h1
  obtain ⟨m, hm⟩ := hT ⟨x * y⁻¹, T.mul_mem hx (T.inv_mem hy)⟩
  have hm' : (x * y⁻¹) ^ (p ^ m) = 1 := by simpa using congrArg Subtype.val hm
  have hcop : Nat.Coprime (p ^ m) (q ^ k) :=
    Nat.Coprime.pow m k ((Nat.coprime_primes hp hq).mpr hpq)
  exact mul_inv_eq_one.mp ((pow_eq_one_iff_of_coprime hcop).mp ⟨hm', hk⟩)

theorem exists_pow_four_mul_three_of_similitude {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    (hq3 : q ≠ 3) {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    (hW : Module.finrank (ZMod q) W = 4) (B : LinearMap.BilinForm (ZMod q) W)
    (hB : ∀ u : W, (∀ v : W, B u v = 0) → u = 0) (halt : ∀ w : W, B w w = 0)
    {P : Subgroup (Module.End (ZMod q) W)ˣ} (hP : IsPGroup 3 P)
    (hPsim : ∀ t ∈ P, ∃ c : ZMod q, ∀ u v : W,
      B ((t : Module.End (ZMod q) W) u) ((t : Module.End (ZMod q) W) v) = c * B u v)
    {g : (Module.End (ZMod q) W)ˣ}
    (hg : g ∈ Subgroup.normalizer (P : Set (Module.End (ZMod q) W)ˣ)) :
    ∃ k : ℕ, ∀ x ∈ P, g ^ (4 * 3 ^ k) * x = x * g ^ (4 * 3 ^ k) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpK : ¬ 3 ∣ Nat.card (ZMod q) := by
    rw [Nat.card_zmod]
    exact fun h => hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : q.Prime)).mp h).symm
  have hPab : IsMulCommutative P :=
    similitudeThreeAbelian hq2 hq3 W hW B hB halt P hP hPsim
  rcases automizer_pow_three_or_four (le_of_eq hW) hpK hP hPab hg with h3 | h4
  · refine ⟨1, fun x hx => ?_⟩
    have hc : Commute (g ^ 3) x := mul_inv_eq_iff_eq_mul.mp (h3 x hx)
    have hc12 : Commute (g ^ (4 * 3 ^ 1)) x := by
      rw [show 4 * 3 ^ 1 = 3 * 4 by norm_num, pow_mul]
      exact hc.pow_left 4
    exact hc12.eq
  · refine ⟨1, fun x hx => ?_⟩
    have hc : Commute (g ^ 4) x := mul_inv_eq_iff_eq_mul.mp (h4 x hx)
    have hc12 : Commute (g ^ (4 * 3 ^ 1)) x := by
      rw [show 4 * 3 ^ 1 = 4 * 3 by norm_num, pow_mul]
      exact hc.pow_left 3
    exact hc12.eq

theorem threeAutFour_of_smallModel {q : ℕ} [Fact q.Prime] (hq3 : q ≠ 3)
    {H : Type} [Group H] [Finite H] {W : Type} [AddCommGroup W] [Module (ZMod q) W]
    [Module.Finite (ZMod q) W] (B : LinearMap.BilinForm (ZMod q) W)
    (ρ : H →* (Module.End (ZMod q) W)ˣ)
    (hρ : ∀ x : H, ρ x = 1 → ∃ k : ℕ, x ^ (q ^ k) = 1)
    (hsim : ∀ x : H, ∃ c : ZMod q, ∀ u v : W,
      B ((ρ x : Module.End (ZMod q) W) u) ((ρ x : Module.End (ZMod q) W) v) = c * B u v)
    (hbound : ∀ P : Subgroup (Module.End (ZMod q) W)ˣ, IsPGroup 3 P →
      (∀ t ∈ P, ∃ c : ZMod q, ∀ u v : W,
        B ((t : Module.End (ZMod q) W) u) ((t : Module.End (ZMod q) W) v) = c * B u v) →
      ∀ y ∈ Subgroup.normalizer (P : Set (Module.End (ZMod q) W)ˣ),
        ∃ k : ℕ, ∀ x ∈ P, y ^ (4 * 3 ^ k) * x = x * y ^ (4 * 3 ^ k))
    (A : Subgroup H) {K : Type} [Group K] (φ : ↥A →* K) (hφ : Function.Surjective φ) :
    ThreeAutFour K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro E hE g hg
  obtain ⟨S, hS, hSE, hlift⟩ := exists_isPGroup_map_eq_and_lift φ hφ hE
  obtain ⟨n, hnN, hng⟩ := hlift g hg
  let ρ' : ↥A →* (Module.End (ZMod q) W)ˣ := ρ.comp A.subtype
  have hρ' : ∀ x : ↥A, ρ' x = 1 → ∃ k : ℕ, x ^ (q ^ k) = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hρ (x : H) hx
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  set P : Subgroup (Module.End (ZMod q) W)ˣ := S.map ρ' with hP
  have hP3 : IsPGroup 3 P := hS.map ρ'
  have hPsim : ∀ t ∈ P, ∃ c : ZMod q, ∀ u v : W,
      B ((t : Module.End (ZMod q) W) u) ((t : Module.End (ZMod q) W) v) = c * B u v := by
    rintro t ⟨s, -, rfl⟩
    exact hsim (s : H)
  have hPN : ρ' n ∈ Subgroup.normalizer (P : Set (Module.End (ZMod q) W)ˣ) :=
    Subgroup.le_normalizer_map ρ' (Subgroup.mem_map_of_mem ρ' hnN)
  obtain ⟨k, hk⟩ := hbound P hP3 hPsim (ρ' n) hPN
  have hcent : ∀ t ∈ S, n ^ (4 * 3 ^ k) * t = t * n ^ (4 * 3 ^ k) := by
    intro t ht
    have hcS : n ^ (4 * 3 ^ k) * t * (n ^ (4 * 3 ^ k))⁻¹ * t⁻¹ ∈ S :=
      S.mul_mem ((Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hnN _) t).mp ht) (S.inv_mem ht)
    have hc1 : n ^ (4 * 3 ^ k) * t * (n ^ (4 * 3 ^ k))⁻¹ * t⁻¹ = 1 := by
      refine eq_of_map_eq_of_isPGroup Nat.prime_three (Fact.out : q.Prime) (Ne.symm hq3) ρ' hρ'
        hS hcS S.one_mem ?_
      have h2 : ρ' (n ^ (4 * 3 ^ k) * t * (n ^ (4 * 3 ^ k))⁻¹ * t⁻¹) = 1 := by
        simp only [map_mul, map_inv, map_pow, map_one]
        rw [hk (ρ' t) ⟨t, ht, rfl⟩]
        group
      simpa using h2
    calc n ^ (4 * 3 ^ k) * t
        = n ^ (4 * 3 ^ k) * t * (n ^ (4 * 3 ^ k))⁻¹ * t⁻¹ * (t * n ^ (4 * 3 ^ k)) := by
          group
      _ = t * n ^ (4 * 3 ^ k) := by rw [hc1, one_mul]
  refine ⟨k, fun e he => ?_⟩
  rw [← hSE] at he
  obtain ⟨s, hs, rfl⟩ := he
  rw [← hng]
  rw [← map_pow, ← map_mul, ← map_mul, hcent s hs]

theorem sevenCentralizesTwo_of_smallModel {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    {H : Type} [Group H] [Finite H] {W : Type} [AddCommGroup W] [Module (ZMod q) W]
    [Module.Finite (ZMod q) W] (ρ : H →* (Module.End (ZMod q) W)ˣ)
    (hρ : ∀ x : H, ρ x = 1 → ∃ k : ℕ, x ^ (q ^ k) = 1)
    (hbound : ∀ R : Subgroup (Module.End (ZMod q) W)ˣ, IsPGroup 2 R →
      ∀ y : (Module.End (ZMod q) W)ˣ, (∃ k : ℕ, y ^ (7 ^ k) = 1) →
      y ∈ Subgroup.normalizer (R : Set (Module.End (ZMod q) W)ˣ) → ∀ x ∈ R, y * x = x * y)
    (A : Subgroup H) {K : Type} [Group K] (φ : ↥A →* K) (hφ : Function.Surjective φ) :
    SevenCentralizesTwo K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro E hE g hg hg7
  obtain ⟨S, hS, hSE, hlift⟩ := exists_isPGroup_map_eq_and_lift φ hφ hE
  obtain ⟨n, hnN, hng⟩ := hlift g hg
  let ρ' : ↥A →* (Module.End (ZMod q) W)ˣ := ρ.comp A.subtype
  have hρ' : ∀ x : ↥A, ρ' x = 1 → ∃ k : ℕ, x ^ (q ^ k) = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hρ (x : H) hx
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  obtain ⟨e, m, hm7, hnm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos n).ne' 7 (by norm_num)
  have hy7 : (n ^ m) ^ (7 ^ e) = 1 := by
    rw [← pow_mul, mul_comm, ← hnm, pow_orderOf_eq_one]
  have hyN : n ^ m ∈ Subgroup.normalizer (S : Set ↥A) := Subgroup.pow_mem _ hnN m
  have hcomm : ∀ x ∈ S.map ρ', ρ' (n ^ m) * x = x * ρ' (n ^ m) :=
    hbound (S.map ρ') (hS.map ρ') (ρ' (n ^ m))
      ⟨e, by rw [← map_pow, hy7, map_one]⟩
      (Subgroup.le_normalizer_map ρ' (Subgroup.mem_map_of_mem ρ' hyN))
  have hyS : ∀ s ∈ S, n ^ m * s = s * n ^ m := by
    intro s hs
    have hcS : n ^ m * s * (n ^ m)⁻¹ * s⁻¹ ∈ S :=
      S.mul_mem ((Subgroup.mem_normalizer_iff.mp hyN s).mp hs) (S.inv_mem hs)
    have hc1 : n ^ m * s * (n ^ m)⁻¹ * s⁻¹ = 1 := by
      refine eq_of_map_eq_of_isPGroup Nat.prime_two (Fact.out : q.Prime) (Ne.symm hq2) ρ' hρ'
        hS hcS S.one_mem ?_
      have h2 : ρ' (n ^ m * s * (n ^ m)⁻¹ * s⁻¹) = 1 := by
        rw [map_mul, map_mul, map_inv, map_mul, map_inv, hcomm (ρ' s) ⟨s, hs, rfl⟩]
        group
      simpa using h2
    calc n ^ m * s = n ^ m * s * (n ^ m)⁻¹ * s⁻¹ * (s * n ^ m) := by group
      _ = s * n ^ m := by rw [hc1, one_mul]
  have hgE : ∀ x ∈ E, Commute (g ^ m) x := by
    intro x hx
    rw [commute_iff_eq]
    rw [← hSE] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    rw [← hng, ← map_pow, ← map_mul, ← map_mul, hyS s hs]
  have hcop : m.Coprime (orderOf g) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hg7)
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 7)).mpr hm7).symm
  obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
  intro x hx
  rw [← hc]
  exact ((hgE x hx).pow_left c).eq

theorem threeAutFour_of_surjective {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    (hlin : GLThreeAutFour q) {V : Type} [Group V] [Finite V] (hV : IsPGroup q V)
    (hr : CFSG.Open.pRank q (⊤ : Subgroup V) ≤ 3) (A : Subgroup (MulAut V)) {K : Type}
    [Group K] (φ : ↥A →* K) (hφ : Function.Surjective φ) : ThreeAutFour K := by
  obtain ⟨W, _, _, _, ρ, hρ, hdim | ⟨h4, B, hB, halt, hsim⟩⟩ := hasSmallSympModel hq2 hV hr
  · refine threeAutFour_of_smallModel hq3 (0 : LinearMap.BilinForm (ZMod q) W) ρ hρ ?_ ?_ A φ hφ
    · intro x
      exact ⟨0, fun u v => by simp⟩
    · intro P hP _ y hy
      exact hlin W hdim P hP y hy
  · refine threeAutFour_of_smallModel hq3 B ρ hρ hsim ?_ A φ hφ
    intro P hP hPsim y hy
    exact exists_pow_four_mul_three_of_similitude hq2 hq3 h4 B hB halt hP hPsim hy

theorem sevenCentralizesTwo_of_surjective {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    (h7 : SevenCentralizesTwoGL q) {V : Type} [Group V] [Finite V] (hV : IsPGroup q V)
    (hr : CFSG.Open.pRank q (⊤ : Subgroup V) ≤ 3) (A : Subgroup (MulAut V)) {K : Type}
    [Group K] (φ : ↥A →* K) (hφ : Function.Surjective φ) : SevenCentralizesTwo K := by
  obtain ⟨W, _, _, _, hW, ρ, hρ⟩ := hasSmallLinearModel hq2 hV hr
  exact sevenCentralizesTwo_of_smallModel hq2 ρ hρ (h7 W hW) A φ hφ

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSectionThree
