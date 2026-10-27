module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.SL3BorelTorus
public import CFSG.LocalAnalysis.UniquenessCase.Lie.Cover
public import CFSG.Quasithin.H13.NQCatL34AutPoint
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXL3R
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.ComponentInitial.LinearFlag

open Subgroup Matrix Module
open CFSG.Open CFSG.ComponentClassification
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsMaxParabolicOver)
open CFSG.LocalAnalysis.UniquenessCase.UC22

open scoped commutatorElement

theorem odd_card_ker_of_le_scalars {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 1 ≤ n) {X : Type*} [Group X]
    {f : SpecialLinearGroup (Fin n) K →* X} (hf : f.ker ≤ scalars n K) :
    Odd (Nat.card f.ker) := by
  have hsc : Nat.card (scalars n K) ∣ Nat.card K - 1 := card_scalars_dvd hn
  exact (RankTwoExceptional.odd_card_sub_one (K := K)).of_dvd_nat
    ((Subgroup.card_dvd_of_le hf).trans hsc)

theorem map_eq_of_map_map_eq {G H : Type*} [Group G] [Finite G] [Group H] {f : G →* H}
    (hf : Function.Surjective f) {Q : Subgroup G} (hQ : f.ker ≤ Q)
    {φ : MulAut G} {ν : MulAut H} (hφν : ∀ x, f (φ x) = ν (f x))
    (hQν : (Q.map f).map ν.toMonoidHom = Q.map f) :
    Q.map φ.toMonoidHom = Q := by
  have hle : Q.map φ.toMonoidHom ≤ Q := by
    rintro _ ⟨q, hq, rfl⟩
    have hmem : f (φ q) ∈ Q.map f := by
      rw [hφν]
      rw [← hQν]
      exact Subgroup.mem_map_of_mem ν.toMonoidHom (Subgroup.mem_map_of_mem f hq)
    have hmemQ : φ q ∈ (Q.map f).comap f := by
      rw [Subgroup.mem_comap]
      exact hmem
    rwa [Subgroup.comap_map_eq_self hQ] at hmemQ
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective])

theorem exists_cover_map_of_odd_closed {S Q : Type} [Group S] [Finite S] [Group Q]
    (hclosed : ∀ (E : Type) [Group E] [Finite E] (π : E →* S), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
      ∃ σ : S →* E, ∀ g, π (σ g) = g)
    (hXp : commutator S = ⊤) (π : S →* Q) (hπ : Function.Surjective π)
    (hπc : π.ker ≤ Subgroup.center S) (hoddKer : Odd (Nat.card π.ker))
    (ρ : S →* Q) (hρ : Function.Surjective ρ) (hρc : ρ.ker ≤ Subgroup.center S) :
    ∃ α : S →* S, Function.Surjective α ∧ α.ker ≤ Subgroup.center S ∧
      ∀ s, π (α s) = ρ s := by
  classical
  let E : Subgroup (S × S) :=
    MonoidHom.eqLocus (π.comp (MonoidHom.fst S S)) (ρ.comp (MonoidHom.snd S S))
  let p : E →* S := (MonoidHom.snd S S).comp E.subtype
  have hp : Function.Surjective p := by
    intro s
    obtain ⟨x, hx⟩ := hπ (ρ s)
    exact ⟨⟨(x, s), hx⟩, rfl⟩
  have hpc : p.ker ≤ Subgroup.center E := by
    intro e he
    have hs : e.1.2 = 1 := he
    have hx : π e.1.1 = 1 := by
      have h : π e.1.1 = ρ e.1.2 := e.2
      rw [hs, map_one] at h
      exact h
    have hxc : e.1.1 ∈ Subgroup.center S := hπc hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply Prod.ext
    · exact Subgroup.mem_center_iff.1 hxc g.1.1
    · simp [hs]
  have hoddp : Odd (Nat.card p.ker) := by
    let fp : p.ker →* π.ker :=
      { toFun := fun y =>
          ⟨((y : E) : S × S).1, by
            have hy2 : ((y : E) : S × S).2 = 1 := by
              have h := y.2
              change p (y : E) = 1 at h
              change ((y : E) : S × S).2 = 1 at h
              exact h
            have h : π ((y : E) : S × S).1 = ρ ((y : E) : S × S).2 := (y : E).2
            rw [hy2, map_one] at h
            exact h⟩
        map_one' := Subtype.ext rfl
        map_mul' _ _ := Subtype.ext rfl }
    have hfp : Function.Injective fp := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg Subtype.val hab
      · have ha : ((a : E) : S × S).2 = 1 := by
          have h := a.2
          change p (a : E) = 1 at h
          change ((a : E) : S × S).2 = 1 at h
          exact h
        have hb : ((b : E) : S × S).2 = 1 := by
          have h := b.2
          change p (b : E) = 1 at h
          change ((b : E) : S × S).2 = 1 at h
          exact h
        rw [ha, hb]
    exact hoddKer.of_dvd_nat (Subgroup.card_dvd_of_injective fp hfp)
  obtain ⟨σ, hσ⟩ := hclosed E p hp hpc hoddp
  let α : S →* S := (MonoidHom.fst S S).comp (E.subtype.comp σ)
  have hαπ : ∀ s, π (α s) = ρ s := by
    intro s
    have h : π ((σ s : E) : S × S).1 = ρ ((σ s : E) : S × S).2 := (σ s).2
    have h2 : ((σ s : E) : S × S).2 = s := hσ s
    rw [h2] at h
    exact h
  refine ⟨α, ?_, ?_, hαπ⟩
  · have hcomm : ∀ x₁ x₂ : S, ⁅x₁, x₂⁆ ∈ α.range := by
      intro x₁ x₂
      obtain ⟨s₁, hs₁⟩ := hρ (π x₁)
      obtain ⟨s₂, hs₂⟩ := hρ (π x₂)
      have hz₁ : (α s₁)⁻¹ * x₁ ∈ Subgroup.center S := by
        apply hπc
        rw [MonoidHom.mem_ker, map_mul, map_inv, hαπ, hs₁]
        exact inv_mul_cancel _
      have hz₂ : (α s₂)⁻¹ * x₂ ∈ Subgroup.center S := by
        apply hπc
        rw [MonoidHom.mem_ker, map_mul, map_inv, hαπ, hs₂]
        exact inv_mul_cancel _
      have e₁ : x₁ = α s₁ * ((α s₁)⁻¹ * x₁) := by group
      have e₂ : x₂ = α s₂ * ((α s₂)⁻¹ * x₂) := by group
      set z₁ := (α s₁)⁻¹ * x₁ with hz₁def
      set z₂ := (α s₂)⁻¹ * x₂ with hz₂def
      have c₁ : ∀ g : S, g * z₁ = z₁ * g := Subgroup.mem_center_iff.1 hz₁
      have c₂ : ∀ g : S, g * z₂ = z₂ * g := Subgroup.mem_center_iff.1 hz₂
      have key : ⁅x₁, x₂⁆ = ⁅α s₁, α s₂⁆ := by
        rw [e₁, e₂]
        exact uc22pwlie_comm_mul_central _ _ _ _ c₁ c₂
      rw [key]
      exact ⟨⁅s₁, s₂⁆, by simp [map_commutatorElement]⟩
    have hle : commutator S ≤ α.range := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_le.2 fun x₁ _ x₂ _ => hcomm x₁ x₂
    intro x
    have hx : x ∈ α.range := by
      have h := hle
      rw [hXp] at h
      exact h (Subgroup.mem_top x)
    exact hx
  · intro s hs
    have : ρ s = 1 := by
      rw [← hαπ]
      have : α s = 1 := hs
      rw [this, map_one]
    exact hρc this

theorem exists_cover_of_odd_center
    {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y) {n : ℕ} (hL : IsL3 (Y ⧸ Subgroup.center Y) n)
    (hodd : Odd (Nat.card (Subgroup.center Y))) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (_ : Y ⧸ Subgroup.center Y ≃* projectiveSL 3 K)
      (α : SpecialLinearGroup (Fin 3) K →* Y),
      Nat.card K = 2 ^ n ∧ Function.Surjective α ∧
        α.ker ≤ scalars 3 K ∧ (scalars 3 K).map α = Subgroup.center Y := by
  classical
  obtain ⟨K, hKf, hKfin, hcard, he⟩ :=
    LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  obtain ⟨e⟩ := he
  haveI : CharP K 2 := uc22pwlie_charP_two hcard
  haveI : Group.IsPerfect Y := ⟨hq.1⟩
  have hsplit : ∀ (E : Type) [Group E] [Finite E]
      (π : E →* SpecialLinearGroup (Fin 3) K), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
      ∃ s : SpecialLinearGroup (Fin 3) K →* E, ∀ g, π (s g) = g := by
    intro E _ _ π hπ hc ho
    obtain ⟨s, hs, -⟩ :=
      SectionRank.EvenCover.even_linear_central_odd_extension_splitting
        (n := 3) (by norm_num) hπ hc ho
    exact ⟨s, hs⟩
  obtain ⟨α, hα, hαc, hαD⟩ :=
    QuasithinUnique.Ch1.exists_cover_map_of_odd_splitting (D := scalars 3 K) hodd e hsplit
  exact ⟨K, hKf, hKfin, inferInstance, e, α, hcard, hα, hαc, hαD⟩


theorem exists_cover_sylow_of_odd_center
    {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y) {n : ℕ} (hL : IsL3 (Y ⧸ Subgroup.center Y) n)
    (hodd : Odd (Nat.card (Subgroup.center Y))) (S : Sylow 2 Y) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (α : SpecialLinearGroup (Fin 3) K →* Y),
      Nat.card K = 2 ^ n ∧ Function.Surjective α ∧ α.ker ≤ scalars 3 K ∧
        (unitriangular 3 K).map α = (S : Subgroup Y) := by
  classical
  obtain ⟨K, hKf, hKfin, hKchar, _, α, hcard, hα, hαc, -⟩ :=
    exists_cover_of_odd_center hq hL hodd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y (Q.mapSurjective hα) S
  refine ⟨K, hKf, hKfin, hKchar,
    (MulAut.conj g).toMonoidHom.comp α, hcard, (MulAut.conj g).surjective.comp hα, ?_, ?_⟩
  · intro s hs
    apply hαc
    have h1 : (MulAut.conj g) (α s) = 1 := hs
    rw [MonoidHom.mem_ker] at hs
    exact (map_eq_one_iff (MulAut.conj g) (MulAut.conj g).injective).1 h1
  · rw [← Subgroup.map_map, ← hQ, ← Sylow.coe_mapSurjective hα]
    have h := congrArg (fun P : Sylow 2 Y => (P : Subgroup Y)) hg
    simpa [coe_sylow_smul] using h

theorem exists_lift_sl3_of_odd_cover
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {Y : Type} [Group Y] [Finite Y]
    (α : SpecialLinearGroup (Fin 3) K →* Y) (hα : Function.Surjective α)
    (hαc : α.ker ≤ scalars 3 K) (hodd : Odd (Nat.card α.ker)) (θ : MulAut Y)
    (hθU : ∀ x, x ∈ (unitriangular 3 K).map α ↔ θ x ∈ (unitriangular 3 K).map α) :
    ∃ ν : MulAut (SpecialLinearGroup (Fin 3) K),
      (∀ s, α (ν s) = θ (α s)) ∧
        ∀ s, s ∈ unitriangular 3 K ↔ ν s ∈ unitriangular 3 K := by
  classical
  have hαc' : α.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) K) :=
    hαc.trans (scalars_le_center 3 K)
  have hρ : Function.Surjective (θ.toMonoidHom.comp α) := θ.surjective.comp hα
  have hρc : (θ.toMonoidHom.comp α).ker ≤
      Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
    intro s hs
    apply hαc'
    have h1 : θ (α s) = 1 := hs
    rw [MonoidHom.mem_ker]
    exact (map_eq_one_iff θ θ.injective).1 h1
  obtain ⟨Ψ, hΨsurj, -, hΨeq⟩ := exists_cover_map_of_odd_closed
    (hclosed := fun E _ _ π hπ hc ho => by
      obtain ⟨s, hs, -⟩ :=
        SectionRank.EvenCover.even_linear_central_odd_extension_splitting
          (n := 3) (by norm_num) hπ hc ho
      exact ⟨s, hs⟩)
    (hXp := CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le
      (K := K) (n := 3) (by norm_num))
    α hα hαc' hodd (θ.toMonoidHom.comp α) hρ hρc
  let ν : MulAut (SpecialLinearGroup (Fin 3) K) :=
    MulEquiv.ofBijective Ψ ⟨Finite.injective_iff_surjective.mpr hΨsurj, hΨsurj⟩
  have hνα : ∀ s, α (ν s) = θ (α s) := fun s => hΨeq s
  have hU : IsPGroup 2 (unitriangular 3 K) := by
    obtain ⟨Q, hQ⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
    rw [← hQ]
    exact Q.isPGroup'
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hU
  have hpow : ∀ s ∈ unitriangular 3 K, s ^ 2 ^ k = 1 := by
    intro s hs
    have h1 := pow_card_eq_one' (G := unitriangular 3 K)
      (x := (⟨s, hs⟩ : unitriangular 3 K))
    rw [hk] at h1
    exact congrArg Subtype.val h1
  have hmap : ∀ s ∈ unitriangular 3 K, ν s ∈ unitriangular 3 K := by
    intro s hs
    obtain ⟨u₀, hu₀, hu₀eq⟩ := (hθU (α s)).1 ⟨s, hs, rfl⟩
    have hzker : u₀⁻¹ * ν s ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hνα, hu₀eq, inv_mul_cancel]
    have hzc : u₀⁻¹ * ν s ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) :=
      hαc' hzker
    have e : ν s = u₀ * (u₀⁻¹ * ν s) := by group
    have hN1 : (ν s) ^ 2 ^ k = 1 := by
      rw [← map_pow, hpow s hs, map_one]
    have hz1 : (u₀⁻¹ * ν s) ^ 2 ^ k = 1 := by
      have h2 : (ν s) ^ 2 ^ k = u₀ ^ 2 ^ k * (u₀⁻¹ * ν s) ^ 2 ^ k := by
        conv_lhs => rw [e]
        exact (Commute.mul_pow (Subgroup.mem_center_iff.1 hzc u₀) _)
      rw [hN1, hpow u₀ hu₀, one_mul] at h2
      exact h2.symm
    have hz3 := uc22pwI3_center_pow_three hzc
    have hord : orderOf (u₀⁻¹ * ν s) ∣ Nat.gcd (2 ^ k) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hz1) (orderOf_dvd_of_pow_eq_one hz3)
    have hgcd : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
    rw [hgcd] at hord
    have hz : u₀⁻¹ * ν s = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hord)
    rw [hz, mul_one] at e
    rw [e]
    exact hu₀
  refine ⟨ν, hνα, fun s => ⟨hmap s, fun hs => ?_⟩⟩
  have hle : (unitriangular 3 K).map ν.toMonoidHom ≤ unitriangular 3 K := by
    rintro _ ⟨t, ht, rfl⟩
    exact hmap t ht
  have heq : (unitriangular 3 K).map ν.toMonoidHom = unitriangular 3 K :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (f := ν.toMonoidHom) ν.injective])
  rw [← heq] at hs
  obtain ⟨t, ht, hts⟩ := hs
  have : t = s := ν.injective hts
  rw [← this]
  exact ht


theorem diagonalTorus_le_upperTriangular {K : Type*} [Field K] :
    SpecialLinearGroup.diagonalTorus K 3 ≤ upperTriangular 3 K := by
  intro g hg
  rw [mem_upperTriangular_iff_isUpperTriangular]
  exact fun i j hij => (SpecialLinearGroup.mem_diagonalTorus_iff.mp hg) (ne_of_gt hij)

theorem diagonalTorus_le_stabilizer {K : Type*} [Field K] (d : ℕ) :
    SpecialLinearGroup.diagonalTorus K 3 ≤ stabilizer (flagSpace 3 K d) :=
  diagonalTorus_le_upperTriangular.trans (upperTriangular_le_stabilizer_flagSpace d)

theorem normalizer_map_unitriangular_le_map_stabilizer {K : Type} [Field K] [Finite K]
    [CharP K 2] {Y : Type} [Group Y] [Finite Y]
    (α : SpecialLinearGroup (Fin 3) K →* Y) (hα : Function.Surjective α)
    (hαc : α.ker ≤ scalars 3 K) {d : ℕ} (hd : 1 ≤ d) (hdn : d < 3) :
    normalizer ((unitriangular 3 K).map α : Set Y) ≤
      (stabilizer (flagSpace 3 K d)).map α := by
  intro x hx
  obtain ⟨e, he, hxe⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwI3_exists_torus_of_mem_normalizer
      α hα (hαc.trans (scalars_le_center 3 K)) hx
  obtain ⟨u, hu, hue⟩ := hxe
  have hud : u * e ∈ stabilizer (flagSpace 3 K d) := by
    refine (stabilizer (flagSpace 3 K d)).mul_mem ?_ ?_
    · exact (upperTriangular_le_stabilizer_flagSpace d)
        ((unitriangular_le_upperTriangular 3 K) hu)
    · exact diagonalTorus_le_stabilizer d he
  refine ⟨u * e, hud, ?_⟩
  have hxeq : x = α u * α e := by rw [hue]; group
  rw [map_mul]
  exact hxeq.symm

theorem isMaxParabolicOver_image_stabilizer {K : Type} [Field K] [Finite K] [CharP K 2]
    {Y : Type} [Group Y] [Finite Y]
    (α : SpecialLinearGroup (Fin 3) K →* Y) (hα : Function.Surjective α)
    (hαc : α.ker ≤ scalars 3 K) {d : ℕ} (hd : 1 ≤ d) (hdn : d < 3) :
    IsMaxParabolicOver (⊤ : Subgroup Y) ((unitriangular 3 K).map α)
      ((stabilizer (flagSpace 3 K d)).map α) := by
  set Q : Subgroup (SpecialLinearGroup (Fin 3) K) := stabilizer (flagSpace 3 K d)
  have hNQ := normalizer_map_unitriangular_le_map_stabilizer α hα hαc hd hdn
  have hkerQ : α.ker ≤ Q :=
    hαc.trans (scalars_le_stabilizer (flagSpace 3 K d))
  have hQne : Q ≠ ⊤ := stabilizer_flagSpace_ne_top hd hdn
  refine ⟨le_top, by simpa using hNQ, ?_, ?_⟩
  · intro htop
    apply hQne
    rw [eq_top_iff]
    intro q _
    have hq : α q ∈ Q.map α := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨q', hq', heq⟩ := hq
    have hz : q * q'⁻¹ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, heq, mul_inv_cancel]
    have hzQ : q * q'⁻¹ ∈ Q := hkerQ hz
    rw [show q = (q * q'⁻¹) * q' by group]
    exact Q.mul_mem hzQ hq'
  · intro R hPR _
    have hQR : Q ≤ R.comap α := by
      intro q hq
      exact hPR (Subgroup.mem_map_of_mem α hq)
    rcases eq_of_stabilizer_flagSpace_le (R.comap α) hQR with h | h
    · left
      rw [← Subgroup.map_comap_eq_self_of_surjective hα R, h]
    · right
      rw [← Subgroup.map_comap_eq_self_of_surjective hα R, h,
        Subgroup.map_top_of_surjective _ hα]

theorem sl3_powerMap_of_fixes_flagParabolics {K : Type} [Field K] [Finite K] [CharP K 2]
    (θ : MulAut (SpecialLinearGroup (Fin 3) K))
    (hθU : ∀ s, s ∈ unitriangular 3 K ↔ θ s ∈ unitriangular 3 K)
    (hQ1 : (stabilizer (flagSpace 3 K 1)).map θ.toMonoidHom =
      stabilizer (flagSpace 3 K 1))
    (hQ2 : (stabilizer (flagSpace 3 K 2)).map θ.toMonoidHom =
      stabilizer (flagSpace 3 K 2)) :
    ∃ j : ℕ, ∀ x ∈ normalizer ((unitriangular 3 K : Subgroup _) : Set _),
      θ x * (x ^ 2 ^ j)⁻¹ ∈ unitriangular 3 K := by
  obtain ⟨A, σ, ε, hε, hθeq⟩ := CFSG.Quasithin.H13.Ch4.KGSL3.exists_standard θ
  obtain ⟨j, hj⟩ := uc22pwlie_ringEquiv_pow σ
  have hε0 : ε = 0 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with h | h
    · exact h
    · exfalso
      have hθeq1 : θ = CatalogueBHigherLinearAction.slConjugation 3 K A *
          CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ *
            CatalogueBGraphForm.slGraphAut 3 K := by
        rw [hθeq, h, pow_one]
      have hQ1img : (stabilizer (flagSpace 3 K 1)).map θ.toMonoidHom =
          stabilizer ((coordImage σ
            (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dotOrth (flagSpace 3 K 1))).map
              (mulVecLin (A : Matrix (Fin 3) (Fin 3) K))) := by
        rw [hθeq1, CFSG.Quasithin.H13.NQCat.L34Aut.map_mul_toMonoidHom',
          CFSG.Quasithin.H13.NQCat.L34Aut.map_mul_toMonoidHom',
          MulEquiv.toMonoidHom_eq_coe, MulEquiv.toMonoidHom_eq_coe,
          MulEquiv.toMonoidHom_eq_coe,
          map_stabilizer_slGraphAut, map_stabilizer_slFieldAut, map_stabilizer_slConjugation]
      set W : Submodule K (Fin 3 → K) := (coordImage σ
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dotOrth (flagSpace 3 K 1))).map
          (mulVecLin (A : Matrix (Fin 3) (Fin 3) K))
      have hstab : stabilizer W = stabilizer (flagSpace 3 K 1) := by
        rw [← hQ1img, hQ1]
      have hproj : projStabilizer W = projStabilizer (flagSpace 3 K 1) := by
        rw [projStabilizer, projStabilizer, hstab]
      have hdot : finrank K (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dotOrth
          (flagSpace 3 K 1)) = 2 := by
        rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.finrank_dotOrth,
          finrank_flagSpace (by omega)]
      have hcoord : finrank K (coordImage σ
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dotOrth
            (flagSpace 3 K 1))) = 2 := by
        rw [CFSG.Quasithin.H13.NQCat.L34Aut.finrank_coordImage, hdot]
      have hW : finrank K W = 2 := by
        rw [show W = _ from rfl,
          CFSG.Quasithin.H13.NQCat.L34Aut.finrank_map_mulVecLin_gl, hcoord]
      have hWdim : 1 ≤ finrank K W ∧ finrank K W < 3 := by
        rw [hW]
        norm_num
      have hFdim : 1 ≤ finrank K (flagSpace 3 K 1) ∧
          finrank K (flagSpace 3 K 1) < 3 := by
        rw [finrank_flagSpace (by omega)]
        norm_num
      have hWeq : W = flagSpace 3 K 1 :=
        CFSG.Quasithin.H13.NQCat.L34Aut.eq_of_projStabilizer_eq hWdim hFdim hproj
      have hdim : finrank K W = 1 := by rw [hWeq, finrank_flagSpace (by omega)]
      omega
  have hmat : ∀ s : SpecialLinearGroup (Fin 3) K,
      (θ s : Matrix (Fin 3) (Fin 3) K) =
        (A : Matrix (Fin 3) (Fin 3) K) * (s : Matrix (Fin 3) (Fin 3) K).map σ *
          ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro s
    rw [hθeq, hε0]
    exact uc22pwI3_matrix_zero A σ s
  have hAup : (A : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := by
    refine uc22pwI3_upper_of_invariant (A : Matrix (Fin 3) (Fin 3) K)
      ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) (Units.mul_inv A) (Units.inv_mul A) ?_
    intro u hu
    have hpre : θ.symm u ∈ unitriangular 3 K := (hθU (θ.symm u)).2 (by simpa using hu)
    refine ⟨((θ.symm u : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).map σ, ?_, ?_⟩
    · intro i k hik
      rw [Matrix.map_apply, hpre.1 i k hik, map_zero]
    · have h := hmat (θ.symm u)
      rw [MulEquiv.apply_symm_apply] at h
      calc (u : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K)
          = ((A : Matrix (Fin 3) (Fin 3) K) *
              ((θ.symm u : SpecialLinearGroup (Fin 3) K) :
                Matrix (Fin 3) (Fin 3) K).map σ *
              ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
                (A : Matrix (Fin 3) (Fin 3) K) := by rw [h]
        _ = (A : Matrix (Fin 3) (Fin 3) K) *
              ((θ.symm u : SpecialLinearGroup (Fin 3) K) :
                Matrix (Fin 3) (Fin 3) K).map σ := by
              rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hpowB : ∀ b ∈ upperTriangular 3 K,
      θ b * (b ^ 2 ^ j)⁻¹ ∈ unitriangular 3 K := by
    intro b hb
    have hbmat : (b : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular :=
      mem_upperTriangular_iff_isUpperTriangular.mp hb
    let D : Matrix (Fin 3) (Fin 3) K := (b : Matrix (Fin 3) (Fin 3) K).map σ
    let D' : Matrix (Fin 3) (Fin 3) K :=
      (((b ^ 2 ^ j)⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    have hDup : D.IsUpperTriangular := fun i k hik => by
      rw [show D i k = σ ((b : Matrix (Fin 3) (Fin 3) K) i k) from rfl,
        hbmat hik, map_zero]
    have hD'up : D'.IsUpperTriangular :=
      coe_inv_isUpperTriangular (A := b ^ 2 ^ j)
        (CFSG.Quasithin.H13.P31X.l3r_pow_upper hbmat (2 ^ j))
    have hdiag : ∀ i : Fin 3, D i i * D' i i = 1 := by
      intro i
      have hbii : (b : Matrix (Fin 3) (Fin 3) K) i i ≠ 0 := by
        have hprod : (∏ k : Fin 3, (b : Matrix (Fin 3) (Fin 3) K) k k) ≠ 0 := by
          rw [← Matrix.det_of_isUpperTriangular hbmat, b.prop]
          exact one_ne_zero
        exact Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
      have hDii : D i i = (b : Matrix (Fin 3) (Fin 3) K) i i ^ 2 ^ j := by
        rw [show D i i = σ ((b : Matrix (Fin 3) (Fin 3) K) i i) from rfl, hj]
      have hD'ii : D' i i = ((b : Matrix (Fin 3) (Fin 3) K) i i ^ 2 ^ j)⁻¹ := by
        have h1 := coe_inv_apply_self_of_isUpperTriangular (A := b ^ 2 ^ j)
          (CFSG.Quasithin.H13.P31X.l3r_pow_upper hbmat (2 ^ j)) i
        rw [CFSG.Quasithin.H13.P31X.l3r_sl_pow_diag hbmat (2 ^ j) i] at h1
        exact eq_inv_of_mul_eq_one_right h1
      rw [hDii, hD'ii, mul_inv_cancel₀ (pow_ne_zero _ hbii)]
    have hgmat : ((θ b * (b ^ 2 ^ j)⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = (A : Matrix (Fin 3) (Fin 3) K) * D *
          ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * D' := by
      change (θ b : Matrix (Fin 3) (Fin 3) K) *
        (((b ^ 2 ^ j)⁻¹ : SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) = _
      rw [hmat b]
    exact uc22pwI3_mem_unitriangular (A := (A : Matrix (Fin 3) (Fin 3) K))
      (B := ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) (D := D) (D' := D')
      hAup hDup hD'up (Units.mul_inv A) hdiag hgmat
  refine ⟨j, fun x hx => ?_⟩
  rw [normalizer_unitriangular] at hx
  exact hpowB x hx

end CFSG.LocalAnalysis.ComponentInitial.LinearFlag
