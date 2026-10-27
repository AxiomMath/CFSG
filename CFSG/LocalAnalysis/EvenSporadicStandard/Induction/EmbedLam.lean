module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Embed
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Lemma36
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35HLambda
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

variable {G : Type} [Group G] [Finite G] {L K : Subgroup G}

theorem isMulCommutative_of_card_le_four {A : Type*} [Group A] [Finite A]
    (h : Nat.card A ≤ 4) : IsMulCommutative A := by
  have hpos : 0 < Nat.card A := Nat.card_pos
  obtain h1 | h2 | h3 | h4 : Nat.card A = 1 ∨ Nat.card A = 2 ∨ Nat.card A = 3 ∨ Nat.card A = 4 :=
    by omega
  · have : Subsingleton A := (Nat.card_eq_one_iff_unique.1 h1).1
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := isCyclic_of_prime_card h2
    infer_instance
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have := isCyclic_of_prime_card h3
    infer_instance
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [h4]; norm_num)

theorem commute_of_isPGroup_of_surjective {C Q : Type*} [Group C] [Finite C] [Group Q]
    {π : C →* Q} (hπ : Function.Surjective π) (hcyc : ∀ S : Sylow 2 C, IsCyclic S)
    {R : Subgroup Q} (hR : IsPGroup 2 R) : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Q := Finite.of_surjective π hπ
  obtain ⟨S, hS⟩ := hR.exists_le_sylow
  obtain ⟨S₀, rfl⟩ := Sylow.mapSurjective_surjective hπ 2 S
  have := hcyc S₀
  have : IsCyclic ↥(S₀.map π) :=
    isCyclic_of_surjective (π.subgroupMap (S₀ : Subgroup C)) (π.subgroupMap_surjective _)
  intro x hx y hy
  have hx' : x ∈ (S₀ : Subgroup C).map π := hS hx
  have hy' : y ∈ (S₀ : Subgroup C).map π := hS hy
  have hc : IsMulCommutative ↥((S₀ : Subgroup C).map π) := inferInstance
  have := hc.is_comm.comm (⟨x, hx'⟩ : ↥((S₀ : Subgroup C).map π)) ⟨y, hy'⟩
  exact congrArg Subtype.val this

omit [Finite G] in
theorem centralizer_le_lam (hKL : K ≤ L) : centralizer (L : Set G) ≤ lam L K := fun _ hx =>
  ⟨Subgroup.centralizer_le_normalizer (L : Set G) hx,
    mem_centralizer_iff.2 fun k hk => mem_centralizer_iff.1 hx k (hKL hk)⟩

omit [Finite G] in
theorem lam_factor (hin : ∀ α ∈ autCentralizer L K, ∃ g : ↥L, α = MulAut.conj g) (hKL : K ≤ L)
    {x : G} (hx : x ∈ lam L K) :
    ∃ g ∈ L ⊓ centralizer (K : Set G), ∃ c ∈ centralizer (L : Set G), x = g * c := by
  have hxN : x ∈ normalizer (L : Set G) := hx.1
  have hxK : x ∈ centralizer (K : Set G) := hx.2
  set α : MulAut ↥L := Subgroup.normalizerMonoidHom L ⟨x, hxN⟩ with hα
  have hαapp : ∀ l : ↥L, ((α l : ↥L) : G) = x * l * x⁻¹ := fun l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨x, hxN⟩ l
  have hαA : α ∈ autCentralizer L K := by
    intro k hk
    apply Subtype.ext
    rw [hαapp]
    have h1 : (k : G) * x = x * k := mem_centralizer_iff.1 hxK k hk
    calc x * (k : G) * x⁻¹ = ((k : G) * x) * x⁻¹ := by rw [h1]
      _ = k := by group
  obtain ⟨g, hg⟩ := hin α hαA
  have hgapp : ∀ l : ↥L, x * l * x⁻¹ = (g : G) * l * (g : G)⁻¹ := fun l => by
    have h1 := hαapp l
    rw [hg] at h1
    rw [← h1]
    rfl
  refine ⟨g, ⟨g.2, mem_centralizer_iff.2 fun k hk => ?_⟩, (g : G)⁻¹ * x, ?_, by group⟩
  · have h1 := hgapp ⟨k, hKL hk⟩
    have h2 : x * k * x⁻¹ = k := by
      have h3 : (k : G) * x = x * k := mem_centralizer_iff.1 hxK k hk
      calc x * k * x⁻¹ = (k * x) * x⁻¹ := by rw [h3]
        _ = k := by group
    have h4 : (g : G) * k * (g : G)⁻¹ = k := by rw [← h1, h2]
    calc (k : G) * (g : G) = ((g : G) * k * (g : G)⁻¹) * (g : G) := by rw [h4]
      _ = (g : G) * k := by group
  · refine mem_centralizer_iff.2 fun l hl => ?_
    have h1 := hgapp ⟨l, hl⟩
    simp only at h1
    calc (l : G) * ((g : G)⁻¹ * x) = (g : G)⁻¹ * ((g : G) * l * (g : G)⁻¹) * x := by group
      _ = (g : G)⁻¹ * (x * l * x⁻¹) * x := by rw [h1]
      _ = ((g : G)⁻¹ * x) * l := by group

omit [Finite G] in
theorem lam_inf_normal :
    ((L ⊓ centralizer (K : Set G)).subgroupOf (lam L K)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : (n : G) ∈ L ⊓ centralizer (K : Set G) := hn
  have hgN : (g : G) ∈ normalizer (L : Set G) := g.2.1
  have hgK : (g : G) ∈ centralizer (K : Set G) := g.2.2
  show ((g * n * g⁻¹ : lam L K) : G) ∈ L ⊓ centralizer (K : Set G)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  refine ⟨(Subgroup.mem_normalizer_iff.1 hgN n).1 hn'.1, mem_centralizer_iff.2 fun k hk => ?_⟩
  have h1 : (k : G) * g = g * k := mem_centralizer_iff.1 hgK k hk
  have h2 : (k : G) * n = n * k := mem_centralizer_iff.1 hn'.2 k hk
  have h4 : (g : G) * k * (g : G)⁻¹ = k := by
    calc (g : G) * k * (g : G)⁻¹ = (k * g) * (g : G)⁻¹ := by rw [h1]
      _ = k := by group
  calc (k : G) * ((g : G) * n * (g : G)⁻¹) = ((k : G) * g) * n * (g : G)⁻¹ := by group
    _ = (g * k) * n * (g : G)⁻¹ := by rw [h1]
    _ = g * (k * n) * (g : G)⁻¹ := by group
    _ = g * (n * k) * (g : G)⁻¹ := by rw [h2]
    _ = ((g : G) * n * (g : G)⁻¹) * ((g : G) * k * (g : G)⁻¹) := by group
    _ = ((g : G) * n * (g : G)⁻¹) * k := by rw [h4]

@[expose] def lamAction (L K : Subgroup G) : lam L K →* autCentralizer L K :=
  ((normalizerMonoidHom L).comp
    (Subgroup.inclusion (inf_le_left : lam L K ≤ normalizer (L : Set G)))).codRestrict
      (autCentralizer L K) (by
    intro g k hk
    have h1 : (k : G) * g = g * k := mem_centralizer_iff.1 g.2.2 k hk
    apply Subtype.ext
    show (g : G) * k * (g : G)⁻¹ = k
    rw [← h1]
    group)

omit [Finite G] in
theorem lamAction_apply (g : lam L K) (l : ↥L) :
    (((lamAction L K g : autCentralizer L K) : MulAut ↥L) l : G) = g * l * (g : G)⁻¹ := rfl

theorem lam_commutator_mem_centralizer {m : ℕ} (hm : m ≤ 2)
    (hA : twoAdic (autCentralizer L K) ≤ m) {P : Subgroup G} (hP : P ≤ lam L K)
    (hP2 : IsPGroup 2 P) :
    ∀ x ∈ P, ∀ y ∈ P, (y * x)⁻¹ * (x * y) ∈ centralizer (L : Set G) := by
  intro x hx y hy
  let ψ : ↥P →* autCentralizer L K := (lamAction L K).comp (Subgroup.inclusion hP)
  have hRp : IsPGroup 2 ψ.range := hP2.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hR4 : Nat.card ψ.range ≤ 4 := by
    obtain ⟨n, hn⟩ := hRp.exists_card_eq
    have hdvd : Nat.card ψ.range ∣ Nat.card (autCentralizer L K) :=
      Subgroup.card_subgroup_dvd_card _
    have hle : n ≤ (Nat.card (autCentralizer L K)).factorization 2 := by
      rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne']
      rwa [hn] at hdvd
    have hn2 : n ≤ 2 := hle.trans (hA.trans hm)
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
      _ = 4 := by norm_num
  have hcomm : IsMulCommutative ψ.range := isMulCommutative_of_card_le_four hR4
  have hxy : ψ ⟨x, hx⟩ * ψ ⟨y, hy⟩ = ψ ⟨y, hy⟩ * ψ ⟨x, hx⟩ := by
    have := hcomm.is_comm.comm (⟨ψ ⟨x, hx⟩, ⟨_, rfl⟩⟩ : ψ.range) ⟨ψ ⟨y, hy⟩, ⟨_, rfl⟩⟩
    exact congrArg Subtype.val this
  have hxP : (⟨x, hP hx⟩ : lam L K) * ⟨y, hP hy⟩ = ⟨x * y, mul_mem (hP hx) (hP hy)⟩ := rfl
  have hyP : (⟨y, hP hy⟩ : lam L K) * ⟨x, hP hx⟩ = ⟨y * x, mul_mem (hP hy) (hP hx)⟩ := rfl
  have hact : lamAction L K ⟨x * y, mul_mem (hP hx) (hP hy)⟩ =
      lamAction L K ⟨y * x, mul_mem (hP hy) (hP hx)⟩ := by
    rw [← hxP, ← hyP, map_mul, map_mul]
    exact hxy
  rw [mem_centralizer_iff]
  intro l hl
  have h1 := congrArg (fun α : autCentralizer L K => ((α : MulAut ↥L) ⟨l, hl⟩ : G)) hact
  simp only [lamAction_apply] at h1
  calc l * ((y * x)⁻¹ * (x * y)) = (y * x)⁻¹ * ((y * x) * l * (y * x)⁻¹) * (x * y) := by group
    _ = (y * x)⁻¹ * ((x * y) * l * (x * y)⁻¹) * (x * y) := by rw [← h1]
    _ = ((y * x)⁻¹ * (x * y)) * l := by group

theorem lam_commute_of_isPGroup {m : ℕ} (hm : m ≤ 2)
    (hcyc : ∀ S : Sylow 2 (centralizer (L : Set G)), IsCyclic S)
    (hA : twoAdic (autCentralizer L K) ≤ m)
    (hin : ∀ α ∈ autCentralizer L K, ∃ g : ↥L, α = MulAut.conj g) (hKL : K ≤ L)
    (hZ : Odd (Nat.card (center ↥L))) {P : Subgroup G} (hP : P ≤ lam L K)
    (hP2 : IsPGroup 2 P) : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  classical
  intro x hx y hy
  set Λ : Subgroup G := lam L K with hΛ
  set D : Subgroup G := L ⊓ centralizer (K : Set G) with hD
  have hDn : (D.subgroupOf Λ).Normal := lam_inf_normal
  let Θ : ↥Λ →* ↥Λ ⧸ D.subgroupOf Λ := QuotientGroup.mk' (D.subgroupOf Λ)
  have hCΛ : centralizer (L : Set G) ≤ Λ := centralizer_le_lam hKL
  let π : ↥(centralizer (L : Set G)) →* ↥Λ ⧸ D.subgroupOf Λ := Θ.comp (Subgroup.inclusion hCΛ)
  have hπ : Function.Surjective π := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨g, hg, c, hc, hzgc⟩ := lam_factor hin hKL z.2
    refine ⟨⟨c, hc⟩, ?_⟩
    show QuotientGroup.mk (Subgroup.inclusion hCΛ ⟨c, hc⟩) = QuotientGroup.mk z
    rw [QuotientGroup.eq]
    have hgc : (g : G) * c = c * g := mem_centralizer_iff.1 hc g hg.1
    show (((Subgroup.inclusion hCΛ ⟨c, hc⟩)⁻¹ * z : ↥Λ) : G) ∈ D
    have hcz : c⁻¹ * (z : G) = g := by
      rw [hzgc, hgc]
      group
    show c⁻¹ * (z : G) ∈ D
    rw [hcz]
    exact hg
  have hP2' : IsPGroup 2 (P.subgroupOf Λ) := hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hP).symm
  have hcommΘ : ∀ a ∈ P.subgroupOf Λ, ∀ b ∈ P.subgroupOf Λ, Θ a * Θ b = Θ b * Θ a :=
    fun a ha b hb => commute_of_isPGroup_of_surjective hπ hcyc (R := (P.subgroupOf Λ).map Θ)
      (hP2'.map Θ) (Θ a) ⟨a, ha, rfl⟩ (Θ b) ⟨b, hb, rfl⟩
  have hxΛ : (⟨x, hP hx⟩ : ↥Λ) ∈ P.subgroupOf Λ := hx
  have hyΛ : (⟨y, hP hy⟩ : ↥Λ) ∈ P.subgroupOf Λ := hy
  have hwD : (y * x)⁻¹ * (x * y) ∈ D := by
    have h1 := hcommΘ _ hxΛ _ hyΛ
    rw [← map_mul, ← map_mul] at h1
    have h2 := QuotientGroup.eq.1 h1.symm
    exact h2
  have hwC := lam_commutator_mem_centralizer hm hA hP hP2 x hx y hy
  have hwP : (y * x)⁻¹ * (x * y) ∈ P :=
    P.mul_mem (P.inv_mem (P.mul_mem hy hx)) (P.mul_mem hx hy)
  have hodd : Odd (orderOf ((y * x)⁻¹ * (x * y))) :=
    odd_orderOf_of_mem_center hZ hwD.1 fun l hl => (mem_centralizer_iff.1 hwC l hl)
  obtain ⟨k, hk⟩ := hP2 ⟨(y * x)⁻¹ * (x * y), hwP⟩
  have hk' : ((y * x)⁻¹ * (x * y)) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hdvd : orderOf ((y * x)⁻¹ * (x * y)) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (orderOf ((y * x)⁻¹ * (x * y))) (2 ^ k) :=
    (Nat.Coprime.pow_right k hodd.coprime_two_right)
  have h1 : orderOf ((y * x)⁻¹ * (x * y)) = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
  have hw1 : (y * x)⁻¹ * (x * y) = 1 := orderOf_eq_one_iff.1 h1
  exact (inv_mul_eq_one.1 hw1).symm

theorem twoSubgroupsAbelian_lam {m : ℕ} (hm : m ≤ 2)
    (hcyc : ∀ S : Sylow 2 (centralizer (L : Set G)), IsCyclic S)
    (hA : twoAdic (autCentralizer L K) ≤ m)
    (hin : ∀ α ∈ autCentralizer L K, ∃ g : ↥L, α = MulAut.conj g) (hKL : K ≤ L)
    (hZ : Odd (Nat.card (center ↥L))) : TwoSubgroupsAbelian ↥(lam L K) := by
  intro P hP2 x hx y hy
  have hle : P.map (lam L K).subtype ≤ lam L K := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  exact Subtype.ext (lam_commute_of_isPGroup hm hcyc hA hin hKL hZ hle (hP2.map _) (x : G)
    ⟨x, hx, rfl⟩ (y : G) ⟨y, hy, rfl⟩)

omit [Finite G] in
theorem mem_centralizer_of_lamAction_eq_one {g : lam L K} (hg : lamAction L K g = 1) :
    (g : G) ∈ centralizer (L : Set G) := by
  rw [mem_centralizer_iff]
  intro l hl
  have h := congrArg (fun α : autCentralizer L K => ((α : MulAut ↥L) ⟨l, hl⟩ : G)) hg
  simp only [lamAction_apply] at h
  have h' : (g : G) * l * (g : G)⁻¹ = l := h
  calc l * (g : G) = ((g : G) * l * (g : G)⁻¹ ) * g := by rw [h']
    _ = (g : G) * l := by group

private theorem isCyclic_of_isPGroup_of_injective' {X Y : Type*} [Group X] [Group Y] [Finite Y]
    (hcyc : ∀ Q : Sylow 2 Y, IsCyclic Q) {f : X →* Y} (hf : Function.Injective f)
    (hX : IsPGroup 2 X) : IsCyclic X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (hX.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  have := hcyc Q
  exact isCyclic_of_injective ((Subgroup.inclusion hQ).comp (MonoidHom.ofInjective hf).toMonoidHom)
    ((Subgroup.inclusion_injective hQ).comp (MonoidHom.ofInjective hf).injective)

theorem elemBound_lam_of_elem {e : ℕ}
    (hcyc : ∀ S : Sylow 2 (centralizer (L : Set G)), IsCyclic S)
    (he : ElemBound e (autCentralizer L K)) : ElemBound (2 * e) ↥(lam L K) := by
  intro E h2 hc
  have hEp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa [pow_two] using h2 x x.2)⟩
  let ψ : ↥E →* autCentralizer L K := (lamAction L K).comp E.subtype
  have hker : Nat.card ψ.ker ≤ 2 := by
    let ι : ψ.ker →* centralizer (L : Set G) :=
      { toFun := fun x => ⟨(((x : E) : lam L K) : G), mem_centralizer_of_lamAction_eq_one x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := by
      intro a b h
      exact Subtype.ext (Subtype.ext (Subtype.ext
        (congrArg (fun z : centralizer (L : Set G) => (z : G)) h)))
    have hcycker : IsCyclic ψ.ker :=
      isCyclic_of_isPGroup_of_injective' hcyc hι (hEp.to_subgroup _)
    obtain ⟨g, hg⟩ := hcycker.exists_generator
    have hg2 : g ^ 2 = 1 := by
      have := h2 (((g : E) : lam L K)) (g : E).2
      apply Subtype.ext
      apply Subtype.ext
      simpa [pow_two] using this
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg2)
  have hrange : Nat.card ψ.range ≤ e := by
    refine he ψ.range ?_ ?_
    · rintro _ ⟨y, rfl⟩
      rw [← map_mul]
      have : y * y = 1 := Subtype.ext (by simpa using h2 y y.2)
      rw [this, map_one]
    · rintro _ ⟨y, rfl⟩ _ ⟨z, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext (hc y y.2 z z.2))
  calc Nat.card E = Nat.card ψ.ker * Nat.card ψ.range :=
        (Subgroup.card_ker_mul_card_range ψ).symm
    _ ≤ 2 * e := Nat.mul_le_mul hker hrange

theorem lamLike_lam_elem {m e : ℕ} (hm : m ≤ 2)
    (hcyc : ∀ S : Sylow 2 (centralizer (L : Set G)), IsCyclic S)
    (hAs : Group.IsSolvable (autCentralizer L K)) (hA : twoAdic (autCentralizer L K) ≤ m)
    (he : ElemBound e (autCentralizer L K))
    (hin : ∀ α ∈ autCentralizer L K, ∃ g : ↥L, α = MulAut.conj g) (hKL : K ≤ L)
    (hZ : Odd (Nat.card (center ↥L))) : LamLike (2 * e) ↥(lam L K) :=
  ⟨lam_isSolvable hcyc hAs, twoSubgroupsAbelian_lam hm hcyc hA hin hKL hZ,
    elemBound_lam_of_elem hcyc he⟩

theorem elemBound_of_twoAdic {m : ℕ} {X : Type} [Group X] [Finite X] {A : Subgroup X}
    (hA : twoAdic A ≤ m) : ElemBound (2 ^ m) ↥A := by
  intro E h2 hc
  have hEp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa [pow_two] using h2 x x.2)⟩
  obtain ⟨n, hn⟩ := hEp.exists_card_eq
  have hdvd : Nat.card E ∣ Nat.card A := Subgroup.card_subgroup_dvd_card _
  have hle : n ≤ (Nat.card A).factorization 2 := by
    rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne']
    rwa [hn] at hdvd
  rw [hn]
  exact Nat.pow_le_pow_right (by norm_num) (hle.trans hA)

end CFSG.EvenSporadicStandard.Induction
