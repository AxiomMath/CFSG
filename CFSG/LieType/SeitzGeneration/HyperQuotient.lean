module

public import CFSG.LieType.SeitzGeneration.HyperLeaf
public import CFSG.LieType.SeitzGeneration.Lift

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbedding

@[expose] def SeitzHyperLie
    (S : ∀ d : TauCeti.ValidLieTypeIndex, ℕ → Subgroup (Cat d) → Prop) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → p ≠ 2 → p ≠ d.1.characteristic →
    ¬ P1ThreeLieList p d → ∀ E : Subgroup (Cat d), IsElemAbelian p E → Nat.card E = p ^ 3 →
      S d p E → HyperGen p (⊤ : Subgroup (Cat d)) E

@[expose] def SeitzHyperInnerCP (Fam : TauCeti.ValidLieTypeIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y] (K E : Subgroup Y), K.Normal →
    Open.IsQuasisimple K → ∀ d : TauCeti.ValidLieTypeIndex, Fam d →
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    p ≠ d.1.characteristic → ¬ P1ThreeLieList p d → IsElemAbelian p E → Nat.card E = p ^ 3 →
    (∀ c ∈ E ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype) →
    E ≤ K ⊔ Subgroup.centralizer (K : Set Y) → p ∣ Nat.card (Subgroup.center K) →
    HyperGen p K E

section Lifting

variable {Y : Type*} [Group Y]

theorem inv_mul_mem_center_of_mul_eq {K : Subgroup Y} {k k' : K} {c c' : Y}
    (hc : c ∈ Subgroup.centralizer (K : Set Y)) (hc' : c' ∈ Subgroup.centralizer (K : Set Y))
    (h : (k : Y) * c = k' * c') : k'⁻¹ * k ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 : (((k'⁻¹ * k : K)) : Y) = c' * c⁻¹ := by
    have h2 : (k' : Y)⁻¹ * k = c' * c⁻¹ := by
      calc (k' : Y)⁻¹ * k = (k' : Y)⁻¹ * ((k : Y) * c) * c⁻¹ := by group
        _ = c' * c⁻¹ := by rw [h]; group
    simpa using h2
  have hcg := (Subgroup.mem_centralizer_iff.1 ((Subgroup.centralizer (K : Set Y)).inv_mem hc))
    g g.2
  have hcg' := (Subgroup.mem_centralizer_iff.1 hc') g g.2
  apply Subtype.ext
  show (g : Y) * ((k'⁻¹ * k : K) : Y) = ((k'⁻¹ * k : K) : Y) * g
  rw [h1]
  calc (g : Y) * (c' * c⁻¹) = ((g : Y) * c') * c⁻¹ := by group
    _ = (c' * g) * c⁻¹ := by rw [hcg']
    _ = c' * ((g : Y) * c⁻¹) := by group
    _ = c' * (c⁻¹ * g) := by rw [hcg]
    _ = c' * c⁻¹ * g := by group

theorem exists_quotientMap {L : Type*} [Group L] {p : ℕ} (hp : p.Prime) {K E : Subgroup Y}
    [K.Normal] (ρ : K →* L) (hρk : ∀ k : K, ρ k = 1 ↔ k ∈ Subgroup.center K)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K)) (hEp : ∀ x ∈ E, x ^ p = 1)
    (hker : ∀ c ∈ E ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype)
    (hin : E ≤ K ⊔ Subgroup.centralizer (K : Set Y)) :
    ∃ ψ : E →* L, Function.Injective ψ ∧ ∀ (x : E) (k : K) (c : Y),
      c ∈ Subgroup.centralizer (K : Set Y) → (x : Y) = k * c → ψ x = ρ k := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hdec : ∀ x : E, ∃ k : K, ∃ c : Y, c ∈ Subgroup.centralizer (K : Set Y) ∧
      (k : Y) * c = x := by
    intro x
    obtain ⟨k, hk, c, hc, hkc⟩ := Subgroup.mem_sup_of_normal_left.1 (hin x.2)
    exact ⟨⟨k, hk⟩, c, hc, hkc⟩
  choose κ γ hγ hκ using hdec
  have hwd : ∀ (x : E) (k : K) (c : Y), c ∈ Subgroup.centralizer (K : Set Y) →
      (x : Y) = k * c → ρ (κ x) = ρ k := by
    intro x k c hc hxkc
    have h1 := (hρk _).2 (inv_mul_mem_center_of_mul_eq (hγ x) hc ((hκ x).trans hxkc))
    rw [map_mul, map_inv] at h1
    exact (inv_mul_eq_one.1 h1).symm
  refine ⟨{ toFun := fun x => ρ (κ x), map_one' := ?_, map_mul' := ?_ }, ?_, ?_⟩
  · exact (hwd 1 1 1 (Subgroup.one_mem _) (by simp)).trans (map_one ρ)
  · intro x y
    have hxy : ((x * y : E) : Y) = ((κ x * κ y : K) : Y) * (γ x * γ y) := by
      have hc := (Subgroup.mem_centralizer_iff.1 (hγ x)) (κ y) (κ y).2
      calc ((x * y : E) : Y) = (x : Y) * y := rfl
        _ = ((κ x : Y) * γ x) * ((κ y : Y) * γ y) := by rw [hκ, hκ]
        _ = (κ x : Y) * ((γ x * κ y) * γ y) := by group
        _ = (κ x : Y) * ((κ y * γ x) * γ y) := by rw [hc]
        _ = ((κ x * κ y : K) : Y) * (γ x * γ y) := by simp only [Subgroup.coe_mul]; group
    show ρ (κ (x * y)) = ρ (κ x) * ρ (κ y)
    rw [hwd (x * y) (κ x * κ y) (γ x * γ y) (Subgroup.mul_mem _ (hγ x) (hγ y)) hxy, map_mul]
  · rw [injective_iff_map_eq_one]
    intro x hx
    have hxZ : κ x ∈ Subgroup.center K := (hρk _).1 hx
    have hxC : (x : Y) ∈ Subgroup.centralizer (K : Set Y) := by
      rw [← hκ x]
      refine Subgroup.mul_mem _ ?_ (hγ x)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hxZ) ⟨g, hg⟩)
    by_contra hx1
    have hx1' : (x : Y) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hord : orderOf (x : Y) = p := orderOf_eq_prime (hEp x x.2) hx1'
    obtain ⟨z, hz, hzx⟩ := hker x ⟨x.2, hxC⟩ hord
    apply hZ
    have hzo : orderOf (⟨z, hz⟩ : Subgroup.center K) = p := by
      rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe z]
      exact (congrArg orderOf hzx).trans hord
    rw [← hzo]
    exact orderOf_dvd_natCard _
  · exact fun x k c hc hxkc => hwd x k c hc hxkc

theorem exists_hyperplane_of_card {p : ℕ} [Fact p.Prime] {E : Subgroup Y}
    (hE : Nat.card E = p ^ 3) : ∃ F : Subgroup Y, F ≤ E ∧ F.relIndex E = p := by
  have hp : p.Prime := Fact.out
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; exact pow_ne_zero 3 hp.ne_zero)
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) p (n := 2)
    (by rw [hE]; exact pow_dvd_pow p (by norm_num))
  refine ⟨H.map E.subtype, Subgroup.map_subtype_le H, ?_⟩
  rw [Subgroup.relIndex, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective E.subtype_injective]
  have h1 := H.card_mul_index
  rw [hH, hE] at h1
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) (by rw [h1]; ring)

theorem pow_eq_one_of_pow_commute {G : Type*} [Group G] {a b g : G}
    (hg : ∀ x : G, x * g = g * x) (h : a * b = b * a * g) (n : ℕ) (hn : a ^ n * b = b * a ^ n) :
    g ^ n = 1 := by
  have key : ∀ m : ℕ, a ^ m * b = b * a ^ m * g ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc a ^ (m + 1) * b = a * (a ^ m * b) := by rw [pow_succ']; group
        _ = a * (b * a ^ m * g ^ m) := by rw [ih]
        _ = (a * b) * a ^ m * g ^ m := by group
        _ = (b * a * g) * a ^ m * g ^ m := by rw [h]
        _ = b * a * (g * a ^ m) * g ^ m := by group
        _ = b * a * (a ^ m * g) * g ^ m := by rw [← hg (a ^ m)]
        _ = b * a ^ (m + 1) * g ^ (m + 1) := by rw [pow_succ', pow_succ]; group
  have h2 := key n
  rw [hn] at h2
  have h3 : b * a ^ n * 1 = b * a ^ n * g ^ n := by rw [mul_one]; exact h2
  exact (mul_left_cancel h3).symm

theorem hyperGen_of_quotientMap {L : Type*} [Group L] {p : ℕ} (hp : p.Prime) {K E : Subgroup Y}
    [K.Normal] (ρ : K →* L) (hρs : Function.Surjective ρ)
    (hρk : ∀ k : K, ρ k = 1 ↔ k ∈ Subgroup.center K)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K)) (hEp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 3) (hin : E ≤ K ⊔ Subgroup.centralizer (K : Set Y))
    (ψ : E →* L) (hspec : ∀ (x : E) (k : K) (c : Y), c ∈ Subgroup.centralizer (K : Set Y) →
      (x : Y) = k * c → ψ x = ρ k)
    (hgen : HyperGen p (⊤ : Subgroup L) ψ.range) : HyperGen p K E := by
  classical
  have hpf : Fact p.Prime := ⟨hp⟩
  set S : Set Y := {k : Y | k ∈ K ∧ ∃ F : Subgroup Y, F ≤ E ∧ F.relIndex E = p ∧
    ∀ f ∈ F, f * k = k * f} with hS
  set M : Subgroup K := (Subgroup.closure S).comap K.subtype with hM
  have hZM : Subgroup.center K ≤ M := by
    obtain ⟨F₁, hF₁E, hF₁r⟩ := exists_hyperplane_of_card (p := p) hcard
    intro z hz
    apply Subgroup.subset_closure
    refine ⟨z.2, F₁, hF₁E, hF₁r, fun f hf => ?_⟩
    obtain ⟨k, hk, c, hc, hkc⟩ := Subgroup.mem_sup_of_normal_left.1 (hin (hF₁E hf))
    have hkz : (k : Y) * z = z * k := congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨k, hk⟩)
    have hcz : (z : Y) * c = c * z := (Subgroup.mem_centralizer_iff.1 hc) z z.2
    rw [← hkc]
    calc k * c * (z : Y) = k * (c * z) := by group
      _ = k * (z * c) := by rw [hcz]
      _ = (k * z) * c := by group
      _ = (z * k) * c := by rw [hkz]
      _ = z * (k * c) := by group
  have hmain : ∀ ℓ : L, (ℓ ∈ (⊤ : Subgroup L) ∧ ∃ F₀ : Subgroup L, F₀ ≤ ψ.range ∧
      F₀.relIndex ψ.range = p ∧ ∀ f ∈ F₀, f * ℓ = ℓ * f) → ℓ ∈ M.map ρ := by
    rintro ℓ ⟨-, F₀, hF₀le, hF₀r, hF₀c⟩
    obtain ⟨k, rfl⟩ := hρs ℓ
    refine ⟨k, ?_, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨k.2, (F₀.comap ψ).map E.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
    · rw [Subgroup.relIndex, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective E.subtype_injective]
      have h1 := Subgroup.relIndex_comap F₀ ψ ⊤
      rw [Subgroup.relIndex_top_right, ← MonoidHom.range_eq_map] at h1
      rw [h1]
      exact hF₀r
    · intro f hf
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hf
      obtain ⟨kx, hkx, c, hc, hkxc⟩ := Subgroup.mem_sup_of_normal_left.1 (hin x.2)
      set k₀ : K := ⟨kx, hkx⟩ with hk₀
      have hψx : ψ x = ρ k₀ := hspec x k₀ c hc hkxc.symm
      have hcomm : ρ k₀ * ρ k = ρ k * ρ k₀ := by
        rw [← hψx]
        exact hF₀c (ψ x) hx
      set g : K := (k * k₀)⁻¹ * (k₀ * k) with hg
      have hgZ : g ∈ Subgroup.center K := by
        refine (hρk _).1 ?_
        rw [hg, map_mul, map_inv, map_mul, map_mul, hcomm, inv_mul_cancel]
      have hgc : ∀ y : K, y * g = g * y := fun y => (Subgroup.mem_center_iff.1 hgZ) y
      have hk₀k : k₀ * k = k * k₀ * g := by rw [hg]; group
      have hxp : (kx : Y) ^ p * c ^ p = 1 := by
        have h1 : ((x : Y)) ^ p = 1 := hEp x x.2
        rw [← hkxc, Commute.mul_pow] at h1
        · exact h1
        · exact (Subgroup.mem_centralizer_iff.1 hc) kx hkx
      have hk₀p : k₀ ^ p ∈ Subgroup.center K := by
        rw [Subgroup.mem_center_iff]
        intro y
        have hcp : (c ^ p) ∈ Subgroup.centralizer (K : Set Y) := Subgroup.pow_mem _ hc p
        have hkp : (kx : Y) ^ p = (c ^ p)⁻¹ := eq_inv_of_mul_eq_one_left hxp
        have hcp' := (Subgroup.mem_centralizer_iff.1
          ((Subgroup.centralizer (K : Set Y)).inv_mem hcp)) y y.2
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_pow]
        rw [show ((k₀ : K) : Y) = kx from rfl, hkp]
        exact hcp'
      have hgp : g ^ p = 1 := by
        refine pow_eq_one_of_pow_commute hgc hk₀k p ?_
        exact (Subgroup.mem_center_iff.1 hk₀p k).symm
      have hg1 : g = 1 := by
        by_contra hne
        apply hZ
        have hne' : (⟨g, hgZ⟩ : Subgroup.center K) ≠ 1 := fun h => hne (congrArg Subtype.val h)
        have hgp' : (⟨g, hgZ⟩ : Subgroup.center K) ^ p = 1 := Subtype.ext hgp
        rw [← orderOf_eq_prime hgp' hne']
        exact orderOf_dvd_natCard _
      have hk₀k' : k₀ * k = k * k₀ := by rw [hk₀k, hg1, mul_one]
      have hkk : (kx : Y) * k = k * kx := congrArg Subtype.val hk₀k'
      have hck : (k : Y) * c = c * k := (Subgroup.mem_centralizer_iff.1 hc) k k.2
      show (E.subtype x : Y) * k = k * (E.subtype x : Y)
      change (x : Y) * k = k * (x : Y)
      rw [← hkxc]
      calc kx * c * (k : Y) = kx * (c * k) := by group
        _ = kx * (k * c) := by rw [hck]
        _ = (kx * k) * c := by group
        _ = (k * kx) * c := by rw [hkk]
        _ = k * (kx * c) := by group
  have hmap : (⊤ : Subgroup L) ≤ M.map ρ :=
    hgen.trans ((Subgroup.closure_le _).2 fun ℓ hℓ => hmain ℓ hℓ)
  have hMtop : M = ⊤ := by
    rw [eq_top_iff]
    intro k _
    obtain ⟨m, hm, hmk⟩ := Subgroup.mem_map.1 (hmap (Subgroup.mem_top (ρ k)))
    have hmZ : m⁻¹ * k ∈ Subgroup.center K :=
      (hρk _).1 (by rw [map_mul, map_inv, hmk, inv_mul_cancel])
    have := M.mul_mem hm (hZM hmZ)
    simpa using this
  intro k hk
  have : (⟨k, hk⟩ : K) ∈ M := hMtop ▸ Subgroup.mem_top _
  exact this

end Lifting

theorem seitzHyperInnerFor_of_lie_cp {Fam : TauCeti.ValidLieTypeIndex → Prop}
    (hL : SeitzHyperLie fun d _ _ => Fam d) (hCP : SeitzHyperInnerCP Fam) :
    SeitzHyperInnerFor Fam := by
  intro p hp hp2 Y _ _ K E hKn hKq d hd he hpd hlist hEa hEc hker hin
  by_cases hz : p ∣ Nat.card (Subgroup.center K)
  · exact hCP p hp hp2 Y K E hKn hKq d hd he hpd hlist hEa hEc hker hin hz
  · have := hKn
    obtain ⟨e⟩ := he
    let ρ : K →* Cat d := (e : K ⧸ Subgroup.center K →* Cat d).comp
      (QuotientGroup.mk' (Subgroup.center K))
    have hρs : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hρk : ∀ k : K, ρ k = 1 ↔ k ∈ Subgroup.center K := by
      intro k
      change e (QuotientGroup.mk' (Subgroup.center K) k) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    obtain ⟨ψ, hψi, hψs⟩ := exists_quotientMap hp ρ hρk hz hEa.2 hker hin
    have hE₀ : IsElemAbelian p ψ.range := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
      · obtain ⟨x, hx⟩ := a.2
        obtain ⟨y, hy⟩ := b.2
        apply Subtype.ext
        show (a : Cat d) * b = b * a
        rw [← hx, ← hy, ← map_mul, ← map_mul, hEa.1.is_comm.comm x y]
      · rintro _ ⟨x, rfl⟩
        rw [← map_pow]
        have : x ^ p = 1 := Subtype.ext (hEa.2 x x.2)
        rw [this, map_one]
    have hcard : Nat.card ψ.range = p ^ 3 :=
      (Nat.card_congr (MonoidHom.ofInjective hψi).toEquiv).symm.trans hEc
    exact hyperGen_of_quotientMap hp ρ hρs hρk hz hEa.2 hEc hin ψ hψs
      (hL d p hp hp2 hpd hlist ψ.range hE₀ hcard hd)

@[expose] def SeitzHyperLieLinear : Prop := SeitzHyperLie fun d _ _ => IsLinearIndex d.1

end CFSG.LieType.SeitzGeneration
