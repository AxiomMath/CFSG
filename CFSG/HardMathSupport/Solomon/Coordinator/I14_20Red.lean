module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Fi22
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I1420

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator

@[expose] def fixedSub {S : Type*} [Group S] (α : MulAut S) : Subgroup S where
  carrier := {s | α s = s}
  mul_mem' := fun {a b} (ha : α a = a) (hb : α b = b) => by
    show α (a * b) = a * b
    rw [map_mul, ha, hb]
  one_mem' := map_one α
  inv_mem' := fun {a} (ha : α a = a) => by
    show α a⁻¹ = a⁻¹
    rw [map_inv, ha]

theorem mem_fixedSub {S : Type*} [Group S] {α : MulAut S} {s : S} : s ∈ fixedSub α ↔ α s = s :=
  Iff.rfl

@[expose] def Fi22Cfg (S : Type) [Group S] (α : MulAut S) : Prop :=
  ∃ H : Subgroup S, IsSubnormal H (fixedSub α) ∧ ∃ (N : Subgroup H) (_ : N.Normal),
    Nat.Coprime 5 (Nat.card N) ∧ Nonempty (H ⧸ N ≃* Fi22G)

theorem fi22Cfg_of_component
    {Y : Type} [Group Y] [Finite Y] (K : Subgroup Y)
    (hq : CFSG.Open.IsQuasisimple ↥K) {x : Y} (hx : x ∈ Subgroup.normalizer (K : Set Y))
    (hnc : ¬ K ≤ Subgroup.centralizer ({x} : Set Y))
    (h5 : K ≤ Subgroup.centralizer ({x ^ 5} : Set Y)) {J : Subgroup Y}
    (hJ : GLAPComponent 5 (K ⊓ Subgroup.centralizer ({x} : Set Y)) J)
    (hFi : IsFiTwentyTwo (↥J ⧸ GLAPPrimeCore 5 ↥J)) :
    ∃ α : MulAut (↥K ⧸ Subgroup.center ↥K), α ^ 5 = 1 ∧ α ≠ 1 ∧
      Fi22Cfg (↥K ⧸ Subgroup.center ↥K) α := by
  obtain ⟨hsimp, hcard⟩ := fi22_facts
  have hcenFi : Subgroup.center Fi22G = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center Fi22G) with h | h
    · exact h
    · exfalso
      have hcomm : ∀ a b : Fi22G, a * b = b * a := fun a b =>
        Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a
      have hprime := @IsSimpleGroup.prime_card _ ⟨fun a b => hcomm a b⟩ hsimp
      rw [hcard] at hprime
      exact absurd hprime (by norm_num)
  obtain ⟨eFi⟩ := hFi
  let α₀ : MulAut ↥K := K.normalizerMonoidHom ⟨x, hx⟩
  have hα₀ : ∀ k : ↥K, ((α₀ k : ↥K) : Y) = x * k * x⁻¹ := fun k => rfl
  have hα₀5 : α₀ ^ 5 = 1 := by
    ext k
    have : (α₀ ^ 5 : MulAut ↥K) = K.normalizerMonoidHom (⟨x, hx⟩ ^ 5) := by rw [map_pow]
    rw [this]
    have hk : ((K.normalizerMonoidHom (⟨x, hx⟩ ^ 5) k : ↥K) : Y) = x ^ 5 * k * (x ^ 5)⁻¹ := rfl
    rw [MulAut.one_apply, hk]
    have := Subgroup.mem_centralizer_iff.1 (h5 k.2) (x ^ 5) rfl
    calc x ^ 5 * (k : Y) * (x ^ 5)⁻¹ = (k : Y) * x ^ 5 * (x ^ 5)⁻¹ := by rw [← this]
      _ = (k : Y) := by group
  have hα₀1 : α₀ ≠ 1 := by
    intro h
    apply hnc
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg (fun φ : MulAut ↥K => ((φ ⟨k, hk⟩ : ↥K) : Y)) h
    simp only [hα₀, MulAut.one_apply] at this
    calc k * x = x * k * x⁻¹ * x := by rw [this]
      _ = x * k := by group
  have hperf : commutator ↥K = ⊤ := hq.1
  let ᾱ : MulAut (↥K ⧸ Subgroup.center ↥K) := autCenterQuot ↥K α₀
  have hinj := autCenterQuot_injective_of_perfect hperf
  refine ⟨ᾱ, ?_, ?_, ?_⟩
  · show (autCenterQuot ↥K α₀) ^ 5 = 1
    rw [← map_pow, hα₀5, map_one]
  · intro h
    apply hα₀1
    apply hinj
    rw [map_one]
    exact h
  · set π : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' _ with hπ
    have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
    have hker : π.ker = Subgroup.center ↥K := QuotientGroup.ker_mk' _
    have hᾱπ : ∀ k : ↥K, ᾱ (π k) = π (α₀ k) := fun k => autCenterQuot_mk α₀ k
    set Ĉ : Subgroup ↥K := (fixedSub ᾱ).comap π with hĈ
    set X : Subgroup Y := K ⊓ Subgroup.centralizer ({x} : Set Y) with hX
    set C₀ : Subgroup ↥K := X.subgroupOf K with hC₀
    have hJX : J ≤ X := hJ.1
    have hJK : J ≤ K := hJX.trans inf_le_left
    have hmemC₀ : ∀ w : ↥K, w ∈ C₀ ↔ α₀ w = w := by
      intro w
      rw [hC₀, Subgroup.mem_subgroupOf, hX, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨-, hc⟩
        apply Subtype.ext
        rw [hα₀]
        calc x * (w : Y) * x⁻¹ = (w : Y) * x * x⁻¹ := by rw [← hc]
          _ = w := by group
      · intro h
        refine ⟨w.2, ?_⟩
        have := congrArg (fun u : ↥K => (u : Y)) h
        simp only [hα₀] at this
        calc (w : Y) * x = x * w * x⁻¹ * x := by rw [this]
          _ = x * w := by group
    have F1 : C₀ ≤ Ĉ := by
      intro k hk
      show ᾱ (π k) = π k
      rw [hᾱπ, (hmemC₀ k).1 hk]
    have hcen : ∀ g : ↥K, g ∈ Ĉ → g⁻¹ * α₀ g ∈ Subgroup.center ↥K := by
      intro g hg
      have h1 : ᾱ (π g) = π g := hg
      rw [hᾱπ] at h1
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, ← h1, inv_mul_cancel]
    have F2 : (C₀.subgroupOf Ĉ).Normal := by
      rw [Subgroup.normal_subgroupOf_iff F1]
      intro h g hh hg
      rw [hmemC₀] at hh ⊢
      have hz := hcen g hg
      set z := g⁻¹ * α₀ g with hzdef
      have hαg : α₀ g = g * z := by rw [hzdef]; group
      have hzc : ∀ k : ↥K, z * k = k * z := fun k => (Subgroup.mem_center_iff.1 hz k).symm
      rw [map_mul, map_mul, map_inv, hh, hαg]
      calc g * z * h * (g * z)⁻¹ = g * (z * h) * z⁻¹ * g⁻¹ := by group
        _ = g * (h * z) * z⁻¹ * g⁻¹ := by rw [hzc h]
        _ = g * h * g⁻¹ := by group
    have F3 : IsSubnormal (J.subgroupOf K) C₀ :=
      isSubnormal_comap' K.subtype hJ.2.1
    have hsn : IsSubnormal (J.subgroupOf K) Ĉ :=
      isSubnormal_trans' F3 (IsSubnormal.step F1 F2 (IsSubnormal.refl Ĉ))
    have hsn2 := isSubnormal_map' π hsn
    rw [hĈ, Subgroup.map_comap_eq_self_of_surjective hπs] at hsn2
    let ψ' : ↥J →* ↥((J.subgroupOf K).map π) :=
      (π.subgroupMap (J.subgroupOf K)).comp (Subgroup.subgroupOfEquivOfLe hJK).symm.toMonoidHom
    have hψ's : Function.Surjective ψ' :=
      (MonoidHom.subgroupMap_surjective π (J.subgroupOf K)).comp
        (Subgroup.subgroupOfEquivOfLe hJK).symm.surjective
    have hψ'val : ∀ j : ↥J, ((ψ' j : ↥((J.subgroupOf K).map π)) : _) = π ⟨j, hJK j.2⟩ :=
      fun j => rfl
    let g : ↥J →* Fi22G := (eFi : ↥J ⧸ GLAPPrimeCore 5 ↥J ≃* Fi22G).toMonoidHom.comp
      (QuotientGroup.mk' (GLAPPrimeCore 5 ↥J))
    have hgs : Function.Surjective g :=
      eFi.surjective.comp (QuotientGroup.mk'_surjective _)
    have hgker : ∀ j : ↥J, g j = 1 ↔ j ∈ GLAPPrimeCore 5 ↥J := by
      intro j
      show eFi (QuotientGroup.mk' (GLAPPrimeCore 5 ↥J) j) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff j
    have hkerle : ψ'.ker ≤ g.ker := by
      intro j hj
      rw [MonoidHom.mem_ker] at hj ⊢
      have h1 : π ⟨j, hJK j.2⟩ = 1 := by
        have := congrArg (fun u : ↥((J.subgroupOf K).map π) => (u : ↥K ⧸ Subgroup.center ↥K)) hj
        simpa [hψ'val] using this
      have hc : (⟨j, hJK j.2⟩ : ↥K) ∈ Subgroup.center ↥K := by
        rw [← hker]; exact h1
      have hgc : g j ∈ Subgroup.center Fi22G := by
        rw [Subgroup.mem_center_iff]
        intro b
        obtain ⟨j', rfl⟩ := hgs b
        rw [← map_mul, ← map_mul]
        have := Subgroup.mem_center_iff.1 hc ⟨j', hJK j'.2⟩
        have h2 : j' * j = j * j' := Subtype.ext (by
          have h3 := congrArg Subtype.val this
          exact h3)
        rw [h2]
      rw [hcenFi, Subgroup.mem_bot] at hgc
      exact hgc
    let f : ↥((J.subgroupOf K).map π) →* Fi22G :=
      (MonoidHom.liftOfSurjective ψ' hψ's) ⟨g, hkerle⟩
    have hfψ : ∀ j : ↥J, f (ψ' j) = g j := fun j =>
      MonoidHom.liftOfRightInverse_comp_apply ψ' _ (Function.rightInverse_surjInv hψ's) ⟨g, hkerle⟩ j
    have hfs : Function.Surjective f := by
      intro b
      obtain ⟨j, rfl⟩ := hgs b
      exact ⟨ψ' j, hfψ j⟩
    have hfle : f.ker ≤ (GLAPPrimeCore 5 ↥J).map ψ' := by
      intro y hy
      obtain ⟨j, rfl⟩ := hψ's y
      rw [MonoidHom.mem_ker, hfψ, hgker] at hy
      exact ⟨j, hy, rfl⟩
    have hcop : Nat.Coprime 5 (Nat.card (GLAPPrimeCore 5 ↥J)) :=
      CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLAPPrimeCore
        (by norm_num) ↥J
    refine ⟨(J.subgroupOf K).map π, hsn2, f.ker, inferInstance, ?_, ⟨QuotientGroup.quotientKerEquivOfSurjective f hfs⟩⟩
    exact Nat.Coprime.coprime_dvd_right
      ((Subgroup.card_dvd_of_le hfle).trans (Subgroup.card_map_dvd _ _)) hcop

end CFSG.HardMathSupport.Solomon.Coordinator.I1420
