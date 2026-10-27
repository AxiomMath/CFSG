module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81LThreeFourAutDefs
import CFSG.LinearAlgebra.SteinbergBQAutomizerPermutation

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

open Module CFSG.LinearAlgebra.SteinbergBQ

private theorem eq_one_of_pow_prime_pow {G : Type*} [Group G] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) {x : G} {m n : ℕ} (hm : x ^ (p ^ m) = 1)
    (hn : x ^ (q ^ n) = 1) : x = 1 :=
  orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow m n ((Nat.coprime_primes hp hq).mpr hpq))
    (orderOf_dvd_of_pow_eq_one hm) (orderOf_dvd_of_pow_eq_one hn))

private theorem eq_of_map_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {V : Type}
    [Group V] {Γ : Type*} [Group Γ] (ρ : MulAut V →* Γ)
    (hρ : ∀ x : MulAut V, ρ x = 1 → ∃ k : ℕ, x ^ (q ^ k) = 1) {A : Subgroup (MulAut V)}
    {T : Subgroup ↥A} (hT : IsPGroup p T) {x y : ↥A} (hx : x ∈ T) (hy : y ∈ T)
    (hxy : ρ (x : MulAut V) = ρ (y : MulAut V)) : x = y := by
  have h1 : ρ ((x * y⁻¹ : ↥A) : MulAut V) = 1 := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hxy, mul_inv_cancel]
  obtain ⟨k, hk⟩ := hρ _ h1
  obtain ⟨m, hm⟩ := hT ⟨x * y⁻¹, T.mul_mem hx (T.inv_mem hy)⟩
  have hm' : (x * y⁻¹) ^ (p ^ m) = 1 := by
    simpa using congrArg Subtype.val hm
  have hk' : (x * y⁻¹) ^ (q ^ k) = 1 := Subtype.ext (by simpa using hk)
  exact mul_inv_eq_one.mp (eq_one_of_pow_prime_pow hp hq hpq hm' hk')

private theorem exists_map_eq_and_lift {H L : Type*} [Group H] [Group L] [Finite H] {p : ℕ}
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

private theorem perm_mul_pow_two_or_three {α : Type*} [Finite α] (hα : Nat.card α ≤ 4)
    {σ τ : Equiv.Perm α} (hσ2 : σ ^ 2 ≠ 1) (hσ3 : σ ^ 3 ≠ 1) (hτ2 : τ ^ 2 ≠ 1)
    (hτ3 : τ ^ 3 ≠ 1) : (σ * τ) ^ 2 = 1 ∨ (σ * τ) ^ 3 = 1 := by
  classical
  let : Fintype α := Fintype.ofFinite α
  let e : Equiv.Perm α ≃* Equiv.Perm (Fin (Fintype.card α)) :=
    Equiv.permCongrHom (Fintype.equivFin α)
  have key : ∀ n, n ≤ 4 → ∀ σ τ : Equiv.Perm (Fin n), σ ^ 2 ≠ 1 → σ ^ 3 ≠ 1 →
      τ ^ 2 ≠ 1 → τ ^ 3 ≠ 1 → (σ * τ) ^ 2 = 1 ∨ (σ * τ) ^ 3 = 1 := by
    intro n hn
    interval_cases n <;> decide +kernel
  have hpow : ∀ (π : Equiv.Perm α) (k : ℕ), e π ^ k = 1 ↔ π ^ k = 1 := fun π k => by
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  rcases key _ (by rwa [← Nat.card_eq_fintype_card]) (e σ) (e τ) ((hpow σ 2).not.mpr hσ2)
      ((hpow σ 3).not.mpr hσ3) ((hpow τ 2).not.mpr hτ2) ((hpow τ 3).not.mpr hτ3) with h | h
  · exact Or.inl ((hpow _ 2).mp (by rwa [map_mul]))
  · exact Or.inr ((hpow _ 3).mp (by rwa [map_mul]))

theorem not_surjective_of_dim_le_three {q : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2)
    (h5 : FiveCentralizesTwo q) {V : Type} [Group V] [Finite V]
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    (hW : Module.finrank (ZMod q) W ≤ 3) (ρ : MulAut V →* (Module.End (ZMod q) W)ˣ)
    (hρ : ∀ x : MulAut V, ρ x = 1 → ∃ k : ℕ, x ^ (q ^ k) = 1)
    (A : Subgroup (MulAut V)) {K : Type} [Group K] (hK : LThreeFourTwoLocal K)
    (φ : ↥A →* K) : ¬ Function.Surjective φ := by
  intro hφ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ' : ↥A →* (Module.End (ZMod q) W)ˣ := ρ.comp A.subtype with hρ'
  obtain ⟨E, hE, yb, hybN, hyb, x, hx, hne⟩ := hK
  obtain ⟨S, hS, hSE, hlift⟩ := exists_map_eq_and_lift φ hφ hE
  obtain ⟨n, hnN, hny⟩ := hlift yb hybN
  obtain ⟨e, m, hm5, hnm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos n).ne' 5 (by norm_num)
  have hy5 : (n ^ m) ^ (5 ^ e) = 1 := by
    rw [← pow_mul, mul_comm, ← hnm, pow_orderOf_eq_one]
  have hyN : n ^ m ∈ Subgroup.normalizer (S : Set ↥A) := Subgroup.pow_mem _ hnN m
  have hcomm := h5 W hW (S.map ρ') (hS.map ρ') (ρ' (n ^ m))
    ⟨e, by rw [← map_pow, hy5, map_one]⟩
    (Subgroup.le_normalizer_map ρ' (Subgroup.mem_map_of_mem ρ' hyN))
  have hyS : ∀ s ∈ S, n ^ m * s = s * n ^ m := by
    intro s hs
    have hcS : n ^ m * s * (n ^ m)⁻¹ * s⁻¹ ∈ S :=
      S.mul_mem ((Subgroup.mem_normalizer_iff.mp hyN s).mp hs) (S.inv_mem hs)
    have hc1 : n ^ m * s * (n ^ m)⁻¹ * s⁻¹ = 1 := by
      refine eq_of_map_eq Nat.prime_two hq.out (Ne.symm hq2) ρ hρ hS hcS S.one_mem ?_
      change ρ' (n ^ m * s * (n ^ m)⁻¹ * s⁻¹) = ρ' 1
      simp only [map_mul, map_inv, map_one]
      rw [hcomm (ρ' s) ⟨s, hs, rfl⟩]
      group
    calc n ^ m * s = n ^ m * s * (n ^ m)⁻¹ * s⁻¹ * (s * n ^ m) := by group
      _ = s * n ^ m := by rw [hc1, one_mul]
  have hcop : m.Coprime (orderOf yb) := by
    rw [hyb]
    exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hm5).symm
  obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hSE] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  have h1 : Commute (yb ^ m) (φ s) := by
    change yb ^ m * φ s = φ s * yb ^ m
    rw [← hny, ← map_pow, ← map_mul, ← map_mul, hyS s hs]
  apply hne
  rw [← hc]
  exact (h1.pow_left c).eq

theorem not_surjective_of_symp {q : ℕ} [hq : Fact q.Prime] (hq3 : q ≠ 3)
    (hA : SimilitudeThreeAbelian q) {V : Type} [Group V] [Finite V]
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    (hW : Module.finrank (ZMod q) W = 4) (ρ : MulAut V →* (Module.End (ZMod q) W)ˣ)
    (hρ : ∀ x : MulAut V, ρ x = 1 → ∃ k : ℕ, x ^ (q ^ k) = 1)
    (B : LinearMap.BilinForm (ZMod q) W) (hB : ∀ u : W, (∀ v : W, B u v = 0) → u = 0)
    (halt : ∀ w : W, B w w = 0)
    (hsim : ∀ x : MulAut V, ∃ c : ZMod q, ∀ u v : W,
      B ((ρ x : Module.End (ZMod q) W) u) ((ρ x : Module.End (ZMod q) W) v) = c * B u v)
    (A : Subgroup (MulAut V)) {K : Type} [Group K] (hK : LThreeFourThreeLocal K)
    (φ : ↥A →* K) : ¬ Function.Surjective φ := by
  classical
  intro hφ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ' : ↥A →* (Module.End (ZMod q) W)ˣ := ρ.comp A.subtype with hρ'
  obtain ⟨E, hE, -, a, haN, b, hbN, hab⟩ := hK
  obtain ⟨T, hT, hTE, hlift⟩ := exists_map_eq_and_lift φ hφ hE
  set P : Subgroup (Module.End (ZMod q) W)ˣ := T.map ρ' with hP
  have hP3 : IsPGroup 3 P := hT.map ρ'
  have hPab : IsMulCommutative P := hA W hW B hB halt P hP3 (by
    rintro _ ⟨x, -, rfl⟩
    exact hsim x)
  set L := AlgebraicClosure (ZMod q)
  have : Finite (Module.End (ZMod q) W) := Module.finite_of_finite (ZMod q)
  have : CharP L q := charP_of_injective_algebraMap (algebraMap (ZMod q) L).injective q
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff L q]
    exact fun h => hq3 ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_three).mp h)
  have hAchar : ((Nat.card P : ℕ) : L) ≠ 0 := by
    obtain ⟨k, hk⟩ := hP3.exists_card_eq
    rw [hk, Nat.cast_pow]
    exact pow_ne_zero k h3L
  have hAcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hPab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcomm : ∀ x ∈ (⊤ : Subgroup P), ∀ y ∈ (⊤ : Subgroup P),
      bcRep L P x * bcRep L P y = bcRep L P y * bcRep L P x := by
    intro x _ y _
    rw [← map_mul, ← map_mul, hPab.is_comm.comm x y]
  have hchar : ((Nat.card (⊤ : Subgroup P) : ℕ) : L) ≠ 0 := by
    rwa [Subgroup.card_top]
  obtain ⟨hfin, hcard⟩ := CFSG.Walter.JT.finite_weights_and_card_le (bcRep L P) ⊤ hcomm hchar
  rw [Module.finrank_baseChange, hW] at hcard
  have hker := ker_weightPermGL L hAcomm hAchar
  let ι : ↥(Subgroup.normalizer (T : Set ↥A)) →*
      ↥(Subgroup.normalizer (P : Set (Module.End (ZMod q) W)ˣ)) :=
    (ρ'.comp (Subgroup.normalizer (T : Set ↥A)).subtype).codRestrict _ fun x =>
      Subgroup.le_normalizer_map ρ' (Subgroup.mem_map_of_mem ρ' x.2)
  let ψ := (weightPermGL L P).comp ι
  have key : ∀ x : ↥(Subgroup.normalizer (T : Set ↥A)), ∀ k : ℕ, ψ x ^ k = 1 →
      ∀ e ∈ E, Commute (φ (x : ↥A) ^ k) e := by
    intro x k hk e he
    have h1 : ι x ^ k ∈ (weightPermGL L P).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hk
    rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h1
    rw [← hTE] at he
    obtain ⟨t, ht, rfl⟩ := he
    have hmem : (x : ↥A) ^ k * t * ((x : ↥A) ^ k)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ x.2 k) t).mp ht
    have h2 : (x : ↥A) ^ k * t * ((x : ↥A) ^ k)⁻¹ = t := by
      refine eq_of_map_eq Nat.prime_three hq.out (Ne.symm hq3) ρ hρ hT hmem ht ?_
      have h3 := h1 (ρ' t) ⟨t, ht, rfl⟩
      have h4 : (((ι x ^ k : ↥(Subgroup.normalizer (P : Set (Module.End (ZMod q) W)ˣ))) :
          (Module.End (ZMod q) W)ˣ)) = ρ' (x : ↥A) ^ k := by
        rw [SubgroupClass.coe_pow]
        rfl
      change ρ' ((x : ↥A) ^ k * t * ((x : ↥A) ^ k)⁻¹) = ρ' t
      rw [map_mul, map_mul, map_inv, map_pow, ← h4, ← h3, mul_inv_cancel_right]
    change φ (x : ↥A) ^ k * φ t = φ t * φ (x : ↥A) ^ k
    rw [← map_pow, ← map_mul, ← map_mul]
    congr 1
    calc (x : ↥A) ^ k * t = (x : ↥A) ^ k * t * ((x : ↥A) ^ k)⁻¹ * (x : ↥A) ^ k := by group
      _ = t * (x : ↥A) ^ k := by rw [h2]
  have hperm : ∀ x : ↥(Subgroup.normalizer (T : Set ↥A)),
      φ (x : ↥A) ∈ ({a, b, a * b} : Set K) → ψ x ^ 2 ≠ 1 ∧ ψ x ^ 3 ≠ 1 := by
    intro x hx
    obtain ⟨h4, e, he, hne⟩ := hab _ hx
    have hc4 : Commute (φ (x : ↥A) ^ 4) e := mul_inv_eq_iff_eq_mul.mp (h4 e he)
    refine ⟨fun h2 => hne (mul_inv_eq_of_eq_mul (key x 2 h2 e he).eq), fun h3 => hne ?_⟩
    have hc1 : Commute (φ (x : ↥A)) e := by
      have h := hc4.mul_left (key x 3 h3 e he).inv_left
      rwa [show φ (x : ↥A) ^ 4 * (φ (x : ↥A) ^ 3)⁻¹ = φ (x : ↥A) by group] at h
    exact mul_inv_eq_of_eq_mul (hc1.pow_left 2).eq
  obtain ⟨a', ha'N, ha'⟩ := hlift a haN
  obtain ⟨b', hb'N, hb'⟩ := hlift b hbN
  obtain ⟨ha2, ha3⟩ := hperm ⟨a', ha'N⟩ (by
    change φ a' ∈ _
    rw [ha']
    simp)
  obtain ⟨hb2, hb3⟩ := hperm ⟨b', hb'N⟩ (by
    change φ b' ∈ _
    rw [hb']
    simp)
  obtain ⟨hab2, hab3⟩ := hperm (⟨a', ha'N⟩ * ⟨b', hb'N⟩) (by
    change φ (a' * b') ∈ _
    rw [map_mul, ha', hb']
    simp)
  rw [map_mul] at hab2 hab3
  haveI := hfin
  rcases perm_mul_pow_two_or_three hcard ha2 ha3 hb2 hb3 with h | h
  · exact hab2 h
  · exact hab3 h

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSection
