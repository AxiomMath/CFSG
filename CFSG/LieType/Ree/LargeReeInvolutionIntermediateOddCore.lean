module

public import CFSG.LieType.Ree.LargeReeExceptionalFullCentralizer
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.LieType.Ree.LargeReeInvolutionFusion

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ReeTag
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

section General

variable {A G : Type*} [Group A] [Group G]

theorem apply_mem_centralizer_of_apply_eq {α : MulAut G} {v x : G} (hv : α v = v)
    (hx : x ∈ Subgroup.centralizer {v}) : α x ∈ Subgroup.centralizer {v} := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  calc α x * v = α x * α v := by rw [hv]
    _ = α (x * v) := (map_mul α x v).symm
    _ = α (v * x) := by rw [hx]
    _ = v * α x := by rw [map_mul, hv]

theorem mem_centralizer_conj_iff (hinj : Function.Injective (MulAut.conj : G →* MulAut G))
    (α : MulAut G) (g : G) : α ∈ Subgroup.centralizer {MulAut.conj g} ↔ α g = g := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  refine ⟨fun h => hinj ?_, fun h => ?_⟩
  · rw [← ReeTag.mulAut_mul_conj_mul_inv α g, h, mul_inv_cancel_right]
  · calc α * MulAut.conj g = α * MulAut.conj g * α⁻¹ * α := by group
      _ = MulAut.conj g * α := by rw [ReeTag.mulAut_mul_conj_mul_inv, h]

theorem oddCore_inf_centralizer_eq_bot_of_conj {Y : Subgroup G} {c u : G} (hc : c ∈ Y)
    (h : CFSG.oddCore ↥(Y ⊓ Subgroup.centralizer {c * u * c⁻¹}) = ⊥) :
    CFSG.oddCore ↥(Y ⊓ Subgroup.centralizer {u}) = ⊥ := by
  have hback : ∀ y ∈ Y ⊓ Subgroup.centralizer {c * u * c⁻¹},
      c⁻¹ * y * c ∈ Y ⊓ Subgroup.centralizer {u} := fun y hy => by
    have h' := conj_mem_inf_centralizer (inv_mem hc) hy
    rwa [inv_inv, show c⁻¹ * (c * u * c⁻¹) * c = u by group] at h'
  let e : ↥(Y ⊓ Subgroup.centralizer {u}) ≃* ↥(Y ⊓ Subgroup.centralizer {c * u * c⁻¹}) :=
    { toFun := fun y => ⟨c * (y : G) * c⁻¹, conj_mem_inf_centralizer hc y.2⟩
      invFun := fun y => ⟨c⁻¹ * (y : G) * c, hback y y.2⟩
      left_inv := fun y => Subtype.ext (by simp only; group)
      right_inv := fun y => Subtype.ext (by simp only; group)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  exact oddCore_eq_bot_of_mulEquiv e h

@[expose] def centralizerRestrictHom (ψ : A →* MulAut G) (v : G) (hv : ∀ a, ψ a v = v) :
    A →* MulAut (Subgroup.centralizer {v}) where
  toFun a :=
    { toFun := fun x => ⟨ψ a (x : G), apply_mem_centralizer_of_apply_eq (hv a) x.2⟩
      invFun := fun x => ⟨ψ a⁻¹ (x : G), apply_mem_centralizer_of_apply_eq (hv a⁻¹) x.2⟩
      left_inv := fun x => Subtype.ext (by
        change ψ a⁻¹ (ψ a (x : G)) = x
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
      right_inv := fun x => Subtype.ext (by
        change ψ a (ψ a⁻¹ (x : G)) = x
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply])
      map_mul' := fun x y => Subtype.ext (map_mul (ψ a) (x : G) (y : G)) }
  map_one' := MulEquiv.ext fun x => Subtype.ext (by
    change ψ 1 (x : G) = x
    rw [map_one, MulAut.one_apply])
  map_mul' a b := MulEquiv.ext fun x => Subtype.ext (by
    change ψ (a * b) (x : G) = ψ a (ψ b (x : G))
    rw [map_mul, MulAut.mul_apply])

theorem mem_range_conj_of_orderOf_eq_two {ψ : A →* MulAut G} (hA : Odd (Nat.card A))
    (Ψ : G ⋊[ψ] A ≃* MulAut G) (hΨ : ∀ x a, Ψ ⟨x, a⟩ = MulAut.conj x * ψ a)
    {u : MulAut G} (hu : orderOf u = 2) : u ∈ (MulAut.conj : G →* MulAut G).range := by
  set p := Ψ.symm u with hp
  have h1 : orderOf p.right ∣ 2 := by
    rw [← hu, ← MulEquiv.orderOf_eq Ψ.symm u]
    exact orderOf_map_dvd SemidirectProduct.rightHom p
  have h2 : orderOf p.right = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact h
    · have hodd : Odd (orderOf p.right) := hA.of_dvd_nat (orderOf_dvd_natCard _)
      rw [h] at hodd
      exact absurd hodd (by decide)
  have hright : p.right = 1 := orderOf_eq_one_iff.1 h2
  refine ⟨p.left, ?_⟩
  calc MulAut.conj p.left = MulAut.conj p.left * ψ p.right := by rw [hright, map_one, mul_one]
    _ = Ψ ⟨p.left, p.right⟩ := (hΨ _ _).symm
    _ = Ψ p := rfl
    _ = u := Ψ.apply_symm_apply u

theorem centralizer_conj_eq_semidirect {ψ : A →* MulAut G}
    (hinj : Function.Injective (MulAut.conj : G →* MulAut G))
    (hNF : ∀ α : MulAut G, ∃! p : G × A, α = MulAut.conj p.1 * ψ p.2)
    {v : G} (hv : ∀ a, ψ a v = v) :
    (∀ α : MulAut G, α ∈ Subgroup.centralizer {MulAut.conj v} ↔
      ∃ x ∈ Subgroup.centralizer {v}, ∃ a : A, α = MulAut.conj x * ψ a) ∧
    (∀ α ∈ Subgroup.centralizer {MulAut.conj v}, ∃! p : Subgroup.centralizer {v} × A,
      α = MulAut.conj (p.1 : G) * ψ p.2) ∧
    ∃ Ψ : Subgroup.centralizer {v} ⋊[centralizerRestrictHom ψ v hv] A ≃*
        Subgroup.centralizer {MulAut.conj v},
      ∀ (x : Subgroup.centralizer {v}) (a : A),
        (Ψ ⟨x, a⟩ : MulAut G) = MulAut.conj (x : G) * ψ a := by
  have hmem : ∀ α : MulAut G, α ∈ Subgroup.centralizer {MulAut.conj v} ↔
      ∃ x ∈ Subgroup.centralizer {v}, ∃ a : A, α = MulAut.conj x * ψ a := by
    intro α
    rw [mem_centralizer_conj_iff hinj]
    constructor
    · intro h
      obtain ⟨⟨x, a⟩, hxa, -⟩ := hNF α
      refine ⟨x, ?_, a, hxa⟩
      rw [hxa, MulAut.mul_apply, hv, MulAut.conj_apply] at h
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * v = x * v * x⁻¹ * x := by group
        _ = v * x := by rw [h]
    · rintro ⟨x, hx, a, rfl⟩
      rw [MulAut.mul_apply, hv, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff.1 hx,
        mul_inv_cancel_right]
  have huniq : ∀ α ∈ Subgroup.centralizer {MulAut.conj v},
      ∃! p : Subgroup.centralizer {v} × A, α = MulAut.conj (p.1 : G) * ψ p.2 := by
    intro α hα
    obtain ⟨x, hx, a, hxa⟩ := (hmem α).1 hα
    obtain ⟨q, -, hq⟩ := hNF α
    refine ⟨(⟨x, hx⟩, a), hxa, fun p hp => ?_⟩
    have h1 := hq ((p.1 : G), p.2) hp
    have h2 := hq (x, a) hxa
    rw [← h2] at h1
    simp only [Prod.mk.injEq] at h1
    exact Prod.ext (Subtype.ext h1.1) h1.2
  let f₁ : Subgroup.centralizer {v} →* MulAut G :=
    MulAut.conj.comp (Subgroup.centralizer {v}).subtype
  have hcompat : ∀ a, f₁.comp (centralizerRestrictHom ψ v hv a).toMonoidHom =
      (MulAut.conj (ψ a)).toMonoidHom.comp f₁ := fun a => MonoidHom.ext fun x =>
    (ReeTag.mulAut_mul_conj_mul_inv (ψ a) (x : G)).symm
  let L := SemidirectProduct.lift f₁ ψ hcompat
  have hL : ∀ p, L p = MulAut.conj (p.left : G) * ψ p.right := fun p => rfl
  have hLinj : Function.Injective L := by
    rw [injective_iff_map_eq_one]
    intro p hp
    rw [hL] at hp
    obtain ⟨q, -, hq⟩ := hNF 1
    have h1 := hq ((p.left : G), p.right) hp.symm
    have h2 := hq (1, 1) (by simp)
    rw [← h2] at h1
    simp only [Prod.mk.injEq] at h1
    exact SemidirectProduct.ext (Subtype.ext h1.1) h1.2
  have hrange : L.range = Subgroup.centralizer {MulAut.conj v} := by
    ext α
    rw [MonoidHom.mem_range, hmem]
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.left, p.left.2, p.right, hL p⟩
    · rintro ⟨x, hx, a, rfl⟩
      exact ⟨⟨⟨x, hx⟩, a⟩, rfl⟩
  exact ⟨hmem, huniq, (MonoidHom.ofInjective hLinj).trans (MulEquiv.subgroupCongr hrange),
    fun x a => rfl⟩

theorem oddCore_inf_centralizer_conj_eq_bot {ψ : A →* MulAut G}
    (hinj : Function.Injective (MulAut.conj : G →* MulAut G))
    (hNF : ∀ α : MulAut G, ∃ p : G × A, α = MulAut.conj p.1 * ψ p.2)
    {v : G} (hv : ∀ a, ψ a v = v)
    (hodd : CFSG.oddCore (Subgroup.centralizer {v} : Subgroup G) = ⊥) {Z : Set G}
    (hZ : ∀ z ∈ Z, z ∈ Subgroup.centralizer {v} ∧
      Subgroup.centralizer {v} ≤ Subgroup.centralizer {z})
    (hfaith : ∀ a, (∀ z ∈ Z, ψ a z = z) → ψ a = 1)
    {Y : Subgroup (MulAut G)} (hY : (MulAut.conj : G →* MulAut G).range ≤ Y) :
    CFSG.oddCore ↥(Y ⊓ Subgroup.centralizer {MulAut.conj v}) = ⊥ := by
  refine oddCore_eq_bot_of_forall fun M hMn hModd => ?_
  have hιmem : ∀ x : Subgroup.centralizer {v},
      MulAut.conj (x : G) ∈ Y ⊓ Subgroup.centralizer {MulAut.conj v} := fun x =>
    Subgroup.mem_inf.2 ⟨hY ⟨x, rfl⟩, by
      rw [mem_centralizer_conj_iff hinj, MulAut.conj_apply,
        Subgroup.mem_centralizer_singleton_iff.1 x.2, mul_inv_cancel_right]⟩
  let ι : Subgroup.centralizer {v} →* ↥(Y ⊓ Subgroup.centralizer {MulAut.conj v}) :=
    (MulAut.conj.comp (Subgroup.centralizer {v}).subtype).codRestrict _ hιmem
  have hιinj : Function.Injective ι := fun x y h =>
    Subtype.ext (hinj (congrArg Subtype.val h))
  have hM'bot : M.comap ι = ⊥ := by
    have hM'odd : Odd (Nat.card (M.comap ι)) := by
      rw [← Subgroup.card_map_of_injective hιinj]
      exact hModd.of_dvd_nat (Subgroup.card_dvd_of_le (Subgroup.map_comap_le ι M))
    have h : M.comap ι ≤ CFSG.oddCore (Subgroup.centralizer {v} : Subgroup G) :=
      le_sSup ⟨hMn.comap ι, hM'odd⟩
    rwa [hodd, le_bot_iff] at h
  have hDv : ∀ r : ↥(Y ⊓ Subgroup.centralizer {MulAut.conj v}), (r : MulAut G) v = v :=
    fun r => (mem_centralizer_conj_iff hinj _ _).1 (Subgroup.mem_inf.1 r.2).2
  have hcomm : ∀ r ∈ M, ∀ x : Subgroup.centralizer {v}, r * ι x = ι x * r := by
    intro r hr x
    obtain ⟨y, hy⟩ : ∃ y : Subgroup.centralizer {v}, ι y = r * ι x * r⁻¹ :=
      ⟨⟨(r : MulAut G) x, apply_mem_centralizer_of_apply_eq (hDv r) x.2⟩, Subtype.ext (by
        change MulAut.conj ((r : MulAut G) x) =
          (r : MulAut G) * MulAut.conj (x : G) * (r : MulAut G)⁻¹
        exact (ReeTag.mulAut_mul_conj_mul_inv _ _).symm)⟩
    have hc : ι (y * x⁻¹) ∈ M := by
      rw [map_mul, map_inv, hy]
      have h1 := hMn.conj_mem r⁻¹ (inv_mem hr) (ι x)
      simpa only [mul_assoc] using mul_mem hr h1
    have hyx : y * x⁻¹ = 1 := by
      have h : y * x⁻¹ ∈ M.comap ι := hc
      rwa [hM'bot, Subgroup.mem_bot] at h
    rw [mul_inv_eq_one] at hyx
    rw [hyx] at hy
    calc r * ι x = r * ι x * r⁻¹ * r := by group
      _ = ι x * r := by rw [← hy]
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  obtain ⟨⟨s, a⟩, hsa⟩ := hNF (r : MulAut G)
  dsimp only at hsa
  have hs : s ∈ Subgroup.centralizer {v} := by
    have h := hDv r
    rw [hsa, MulAut.mul_apply, hv, MulAut.conj_apply] at h
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc s * v = s * v * s⁻¹ * s := by group
      _ = v * s := by rw [h]
  have hrz : ∀ z ∈ Z, (r : MulAut G) z = z := by
    intro z hz
    have h := congrArg Subtype.val (hcomm r hr ⟨z, (hZ z hz).1⟩)
    change (r : MulAut G) * MulAut.conj z = MulAut.conj z * (r : MulAut G) at h
    apply hinj
    rw [← ReeTag.mulAut_mul_conj_mul_inv (r : MulAut G) z, h, mul_inv_cancel_right]
  have hψ : ψ a = 1 := by
    refine hfaith a fun z hz => ?_
    have h := hrz z hz
    rw [hsa, MulAut.mul_apply, MulAut.conj_apply] at h
    have hsz : s * z = z * s := Subgroup.mem_centralizer_singleton_iff.1 ((hZ z hz).2 hs)
    calc ψ a z = s⁻¹ * (s * ψ a z * s⁻¹) * s := by group
      _ = s⁻¹ * (z * s) := by rw [h, mul_assoc]
      _ = z := by rw [← hsz]; group
  have hrι : r = ι ⟨s, hs⟩ := Subtype.ext (by
    change (r : MulAut G) = MulAut.conj s
    rw [hsa, hψ, mul_one])
  have h : (⟨s, hs⟩ : Subgroup.centralizer {v}) ∈ M.comap ι := by
    change ι ⟨s, hs⟩ ∈ M
    rw [← hrι]
    exact hr
  rw [hM'bot, Subgroup.mem_bot] at h
  rw [hrι, h, map_one]

end General

section Sub

variable {M : Type*} [Group M] {Γ : Subgroup M}

theorem mem_centralizer_subtype_iff {x v : Γ} :
    x ∈ Subgroup.centralizer {v} ↔ (x : M) ∈ Subgroup.centralizer {(v : M)} := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext_iff

@[expose] def centralizerEquivInf (v : Γ) :
    Subgroup.centralizer {v} ≃* ↥(Γ ⊓ Subgroup.centralizer {(v : M)}) where
  toFun x := ⟨x.1.1, Subgroup.mem_inf.2 ⟨x.1.2, mem_centralizer_subtype_iff.1 x.2⟩⟩
  invFun y := ⟨⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩,
    mem_centralizer_subtype_iff.2 (Subgroup.mem_inf.1 y.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end Sub

section Field

variable {m : ℕ} {K : Type} [Field K]

theorem units_map_entrywiseHom_pinnedX
    (σ : K →+* K) (α : Fin F4.tag.rank → ℤ) (c : K) :
    Units.map (entrywiseHom σ) (pinnedX F4.tag K α c) = pinnedX F4.tag K α (σ c) :=
  Units.ext (entrywise_pinnedX σ α c)

theorem units_map_centralZ
    (β : K ≃+* K) (c : K) :
    Units.map (entrywiseHom β.toRingHom) (centralZ K m c) = centralZ K m (β c) := by
  simp only [centralZ, map_mul, units_map_entrywiseHom_pinnedX, map_pow]
  rfl

theorem units_map_sylowL
    (β : K ≃+* K) (c : K) :
    Units.map (entrywiseHom β.toRingHom) (sylowL m K c) = sylowL m K (β c) := by
  simp only [sylowL, sylowX, largeReeSigma, map_mul, units_map_entrywiseHom_pinnedX, map_pow]
  rfl

variable [CharP K F4.prime]

theorem sylowL_injective
    : Function.Injective (sylowL m K) := fun l l' h =>
  twoCoordG_injective 3 (by rwa [← sylowL_eq, ← sylowL_eq])

end Field

section Rep

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem intermediate_centralizer_data
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {w : K → ModGL F4.tag K} (hw : Function.Injective w)
    (hwβ : ∀ (β : K ≃+* K) (c : K), Units.map (entrywiseHom β.toRingHom) (w c) = w (β c))
    (hwc : ∀ c, w c ∈ F4.reeGamma K m ⊓ Subgroup.centralizer {w 1} ∧
      F4.reeGamma K m ⊓ Subgroup.centralizer {w 1} ≤ Subgroup.centralizer {w c})
    (hodd : CFSG.oddCore ↥(F4.reeGamma K m ⊓ Subgroup.centralizer {w 1}) = ⊥)
    (v : F4.reeGamma K m) (hv : (v : ModGL F4.tag K) = w 1) :
    ∃ hfix : ∀ β : K ≃+* K, F4.reeGammaFieldAutHom K m β v = v,
      (∀ Y : Subgroup (MulAut (F4.reeGamma K m)),
        (MulAut.conj : F4.reeGamma K m →* MulAut (F4.reeGamma K m)).range ≤ Y →
          CFSG.oddCore ↥(Y ⊓ Subgroup.centralizer {MulAut.conj v}) = ⊥) ∧
      (∀ α : MulAut (F4.reeGamma K m), α ∈ Subgroup.centralizer {MulAut.conj v} ↔
        ∃ x ∈ Subgroup.centralizer {v}, ∃ β : K ≃+* K,
          α = MulAut.conj x * F4.reeGammaFieldAut K m β) ∧
      (∀ α ∈ Subgroup.centralizer {MulAut.conj v},
        ∃! p : Subgroup.centralizer {v} × (K ≃+* K),
          α = MulAut.conj (p.1 : F4.reeGamma K m) * F4.reeGammaFieldAut K m p.2) ∧
      ∃ Ψ : Subgroup.centralizer {v} ⋊[centralizerRestrictHom (F4.reeGammaFieldAutHom K m) v hfix]
          (K ≃+* K) ≃* Subgroup.centralizer {MulAut.conj v},
        ∀ (x : Subgroup.centralizer {v}) (β : K ≃+* K),
          (Ψ ⟨x, β⟩ : MulAut (F4.reeGamma K m)) =
            MulAut.conj (x : F4.reeGamma K m) * F4.reeGammaFieldAut K m β := by
  obtain ⟨v, hvmem⟩ := v
  change v = w 1 at hv
  subst hv
  set Γ := F4.reeGamma K m
  set v₀ : Γ := ⟨w 1, hvmem⟩ with hv₀
  have hinj := conj_injective_of_center_eq_bot (large_Ree_fixed_group_center_trivial m K hK)
  obtain ⟨-, hNF, -⟩ := large_Ree_full_inner_field_automorphism_normal_form m hm K hK
  have hfix : ∀ β : K ≃+* K, F4.reeGammaFieldAutHom K m β v₀ = v₀ := fun β => Subtype.ext (by
    change Units.map (entrywiseHom β.toRingHom) (w 1) = w 1
    rw [hwβ, map_one])
  have hoddΓ : CFSG.oddCore (Subgroup.centralizer {v₀} : Subgroup Γ) = ⊥ :=
    oddCore_eq_bot_of_mulEquiv (centralizerEquivInf v₀) hodd
  set Z : Set Γ := {z | ∃ c, (z : ModGL F4.tag K) = w c} with hZdef
  have hZ : ∀ z ∈ Z, z ∈ Subgroup.centralizer {v₀} ∧
      Subgroup.centralizer {v₀} ≤ Subgroup.centralizer {z} := by
    rintro z ⟨c, hc⟩
    refine ⟨mem_centralizer_subtype_iff.2 ?_, fun s hs => mem_centralizer_subtype_iff.2 ?_⟩
    · rw [hc]
      exact (Subgroup.mem_inf.1 (hwc c).1).2
    · rw [hc]
      exact (hwc c).2 (Subgroup.mem_inf.2 ⟨s.2, mem_centralizer_subtype_iff.1 hs⟩)
  have hfaith : ∀ β : K ≃+* K, (∀ z ∈ Z, F4.reeGammaFieldAutHom K m β z = z) →
      F4.reeGammaFieldAutHom K m β = 1 := by
    intro β hβ
    have hβ1 : β = 1 := RingEquiv.ext fun c => by
      have h := congrArg Subtype.val (hβ ⟨w c, (Subgroup.mem_inf.1 (hwc c).1).1⟩ ⟨c, rfl⟩)
      change Units.map (entrywiseHom β.toRingHom) (w c) = w c at h
      rw [hwβ] at h
      exact hw h
    rw [hβ1, map_one]
  obtain ⟨hmem, huniq, hΨ⟩ :=
    centralizer_conj_eq_semidirect (ψ := F4.reeGammaFieldAutHom K m) hinj hNF hfix
  exact ⟨hfix, fun Y hY => oddCore_inf_centralizer_conj_eq_bot (ψ := F4.reeGammaFieldAutHom K m)
    hinj (fun α => (hNF α).exists) hfix hoddΓ hZ hfaith hY, hmem, huniq, hΨ⟩

end Rep

theorem large_Ree_all_intermediate_involution_centralizers_odd_core_free
    (m : ℕ) (hm : 1 ≤ m)
    (K : Type) [Field K] [Finite K] [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    (∀ Y : Subgroup (MulAut (F4.reeGamma K m)),
      (MulAut.conj : F4.reeGamma K m →* MulAut (F4.reeGamma K m)).range ≤ Y →
      ∀ u ∈ Y, orderOf u = 2 →
        u ∈ (MulAut.conj : F4.reeGamma K m →* MulAut (F4.reeGamma K m)).range ∧
        CFSG.oddCore ↥(Y ⊓ Subgroup.centralizer {u}) = ⊥ ∧
        CFSG.piCore {p : Nat.Primes | p.val ≠ 2} ↥(Y ⊓ Subgroup.centralizer {u}) = ⊥) ∧
    ∀ v : F4.reeGamma K m,
      ((v : ModGL F4.tag K) = centralZ K m 1 ∨ (v : ModGL F4.tag K) = sylowL m K 1) →
      ∃ hfix : ∀ β : K ≃+* K, F4.reeGammaFieldAutHom K m β v = v,
        (∀ α : MulAut (F4.reeGamma K m), α ∈ Subgroup.centralizer {MulAut.conj v} ↔
          ∃ x ∈ Subgroup.centralizer {v}, ∃ β : K ≃+* K,
            α = MulAut.conj x * F4.reeGammaFieldAut K m β) ∧
        (∀ α ∈ Subgroup.centralizer {MulAut.conj v},
          ∃! p : Subgroup.centralizer {v} × (K ≃+* K),
            α = MulAut.conj (p.1 : F4.reeGamma K m) * F4.reeGammaFieldAut K m p.2) ∧
        (∀ (β : K ≃+* K) (x : Subgroup.centralizer {v}),
          (((centralizerRestrictHom (F4.reeGammaFieldAutHom K m) v hfix β x :
              Subgroup.centralizer {v}) : F4.reeGamma K m) : ModGL F4.tag K) =
            Units.map (entrywiseHom β.toRingHom) ((x : F4.reeGamma K m) : ModGL F4.tag K)) ∧
        ∃ Ψ : Subgroup.centralizer {v} ⋊[centralizerRestrictHom (F4.reeGammaFieldAutHom K m) v
            hfix] (K ≃+* K) ≃* Subgroup.centralizer {MulAut.conj v},
          ∀ (x : Subgroup.centralizer {v}) (β : K ≃+* K),
            (Ψ ⟨x, β⟩ : MulAut (F4.reeGamma K m)) =
              MulAut.conj (x : F4.reeGamma K m) * F4.reeGammaFieldAut K m β := by
  set Γ := F4.reeGamma K m
  have hinj := conj_injective_of_center_eq_bot (large_Ree_fixed_group_center_trivial m K hK)
  obtain ⟨-, -, ⟨Ψ, hΨ⟩, -⟩ := large_Ree_full_inner_field_automorphism_normal_form m hm K hK
  obtain ⟨-, -, -, -, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 2 * m + 1) hK
  have hA : Odd (Nat.card (K ≃+* K)) := by
    rw [hcardAut]
    exact odd_two_mul_add_one m
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hzodd, htodd, hzc, htc, -, -, -⟩ :=
    large_Ree_two_involution_centralizers m hm K hK
  have hZ := intermediate_centralizer_data hm hK centralZ_injective units_map_centralZ hzc hzodd
  have hT := intermediate_centralizer_data hm hK sylowL_injective units_map_sylowL htc htodd
  refine ⟨fun Y hY u _ hu2 => ?_, fun v hv => ?_⟩
  · have hinner := mem_range_conj_of_orderOf_eq_two hA Ψ hΨ hu2
    obtain ⟨x, rfl⟩ := hinner
    have hx2 : orderOf x = 2 := by rwa [orderOf_injective MulAut.conj hinj x] at hu2
    have hxsq : (x : ModGL F4.tag K) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← hx2, pow_orderOf_eq_one, Subgroup.coe_one]
    have hxne : (x : ModGL F4.tag K) ≠ 1 := by
      intro h
      have h1 : x = 1 := Subtype.ext h
      rw [h1, orderOf_one] at hx2
      exact absurd hx2 (by decide)
    have key : ∀ (w : ModGL F4.tag K) (hw : w ∈ Γ),
        (∀ Y' : Subgroup (MulAut Γ), (MulAut.conj : Γ →* MulAut Γ).range ≤ Y' →
          CFSG.oddCore ↥(Y' ⊓ Subgroup.centralizer {MulAut.conj (⟨w, hw⟩ : Γ)}) = ⊥) →
        (∃ g ∈ Γ, g * (x : ModGL F4.tag K) * g⁻¹ = w) →
        CFSG.oddCore ↥(Y ⊓ Subgroup.centralizer {MulAut.conj x}) = ⊥ := by
      rintro w hw hcore ⟨g, hg, hgx⟩
      refine oddCore_inf_centralizer_eq_bot_of_conj (c := MulAut.conj (⟨g, hg⟩ : Γ))
        (hY ⟨_, rfl⟩) ?_
      have h : MulAut.conj (⟨g, hg⟩ : Γ) * MulAut.conj x * (MulAut.conj (⟨g, hg⟩ : Γ))⁻¹ =
          MulAut.conj (⟨w, hw⟩ : Γ) := by
        rw [← map_inv, ← map_mul, ← map_mul]
        exact congrArg MulAut.conj (Subtype.ext hgx)
      rw [h]
      exact hcore Y hY
    have hodd : CFSG.oddCore ↥(Y ⊓ Subgroup.centralizer {MulAut.conj x}) = ⊥ := by
      rcases involution_conj_zOne_or_tOne hm hK x.2 hxsq hxne with h | h
      · obtain ⟨-, hcore, -⟩ := hZ ⟨_, (Subgroup.mem_inf.1 (hzc 1).1).1⟩ rfl
        rw [sylowH_zero_eq_centralZ] at h
        exact key _ _ hcore h
      · obtain ⟨-, hcore, -⟩ := hT ⟨_, (Subgroup.mem_inf.1 (htc 1).1).1⟩ rfl
        exact key _ _ hcore h
    exact ⟨⟨x, rfl⟩, hodd, by rw [← CFSG.oddCore_eq_piCore, hodd]⟩
  · have hdata := hv.elim (hZ v) (hT v)
    obtain ⟨hfix, -, hmem, huniq, hΨv⟩ := hdata
    exact ⟨hfix, hmem, huniq, fun β x => rfl, hΨv⟩

end CFSG.LieType.Ree.LargeReeInvolution
