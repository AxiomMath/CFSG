module

public import CFSG.Fischer.Pairs

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X : Type} [Group X] {E : Set X} (hP : Pair X E) {e : X} (he : e ∈ E) {M : Subgroup X}
  (hcent : ∀ c ∈ Subgroup.centralizer ({e} : Set X), c ∈ M ∨ c * e ∈ M)
  (hcomm : ∀ m ∈ M, m * e = e * m) (heM : e ∉ M) (hmem : ∀ f ∈ LocalClass E e, f * e ∈ M)
  [hS : IsSimpleGroup M] (hZ : Subgroup.center M = ⊥)
  (hne : ∃ f₁ ∈ LocalClass E e, ∃ f₂ ∈ LocalClass E e, f₁ ≠ f₂)

section

include hP

theorem conj_mem_localClass_of_commute {m : X} (hm : m * e = e * m) {f : X}
    (hf : f ∈ LocalClass E e) : m * f * m⁻¹ ∈ LocalClass E e := by
  have hm' : m⁻¹ * e = e * m⁻¹ := (Commute.inv_left (hm : Commute m e)).eq
  refine ⟨Pair.conj_mem hP hf.1 m, fun h => hf.2.1 ?_, ?_⟩
  · calc f = m⁻¹ * (m * f * m⁻¹) * m := by group
      _ = m⁻¹ * e * m := by rw [h]
      _ = e := by rw [hm', mul_assoc, inv_mul_cancel, mul_one]
  · have hfe : f * e = e * f := hf.2.2
    calc m * f * m⁻¹ * e = m * f * (m⁻¹ * e) := by group
      _ = m * (f * e) * m⁻¹ := by rw [hm']; group
      _ = m * e * f * m⁻¹ := by rw [hfe]; group
      _ = e * (m * f * m⁻¹) := by rw [hm]; group

theorem conj_mem_localGroup_of_commute {m : X} (hm : m * e = e * m) {x : X}
    (hx : x ∈ LocalGroup E e) : m * x * m⁻¹ ∈ LocalGroup E e := by
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact Subgroup.subset_closure (conj_mem_localClass_of_commute hP hm hy)
  | one => simp
  | mul y z _ _ hy hz =>
    have : m * (y * z) * m⁻¹ = (m * y * m⁻¹) * (m * z * m⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hy hz
  | inv y _ hy =>
    have : m * y⁻¹ * m⁻¹ = (m * y * m⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hy

end

theorem localGroup_le_centralizer : LocalGroup E e ≤ Subgroup.centralizer ({e} : Set X) := by
  rw [LocalGroup, Subgroup.closure_le]
  intro f hf
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact hf.2.2

include hP he hcomm hmem hS hne in
theorem le_localGroup : M ≤ LocalGroup E e := by
  obtain ⟨f₁, hf₁, f₂, hf₂, h12⟩ := hne
  have he2 : e * e = 1 := Pair.mul_self hP he
  let N : Subgroup M := (LocalGroup E e).subgroupOf M
  have hN : N.Normal := ⟨fun x hx m => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact conj_mem_localGroup_of_commute hP (hcomm m m.2) hx⟩
  have hprod : f₁ * f₂ = (f₁ * e) * (f₂ * e) := by
    have : f₂ * e = e * f₂ := hf₂.2.2
    calc f₁ * f₂ = f₁ * (f₂ * (e * e)) := by rw [he2, mul_one]
      _ = f₁ * ((f₂ * e) * e) := by group
      _ = f₁ * ((e * f₂) * e) := by rw [this]
      _ = (f₁ * e) * (f₂ * e) := by group
  have hmemM : f₁ * f₂ ∈ M := by
    rw [hprod]; exact M.mul_mem (hmem f₁ hf₁) (hmem f₂ hf₂)
  have hmemG : f₁ * f₂ ∈ LocalGroup E e :=
    (LocalGroup E e).mul_mem (Subgroup.subset_closure hf₁) (Subgroup.subset_closure hf₂)
  have hne1 : (⟨f₁ * f₂, hmemM⟩ : M) ≠ 1 := by
    intro h
    have h' : f₁ * f₂ = 1 := congrArg Subtype.val h
    apply h12
    have h2 : f₂ * f₂ = 1 := Pair.mul_self hP hf₂.1
    calc f₁ = f₁ * (f₂ * f₂) := by rw [h2, mul_one]
      _ = (f₁ * f₂) * f₂ := by group
      _ = f₂ := by rw [h', one_mul]
  have hNtop : N = ⊤ := by
    rcases hN.eq_bot_or_eq_top with h | h
    · exfalso
      apply hne1
      have : (⟨f₁ * f₂, hmemM⟩ : M) ∈ N := Subgroup.mem_subgroupOf.2 hmemG
      rw [h] at this
      exact Subgroup.mem_bot.1 this
    · exact h
  intro m hm
  have : (⟨m, hm⟩ : M) ∈ N := by rw [hNtop]; trivial
  exact Subgroup.mem_subgroupOf.1 this

include hP he hcomm hmem hS hne in
theorem mem_localGroup_self : e ∈ LocalGroup E e := by
  have hM := le_localGroup hP he hcomm hmem hne
  obtain ⟨f₁, hf₁, -⟩ := hne
  have h1 : f₁ * e ∈ LocalGroup E e := hM (hmem f₁ hf₁)
  have h2 : f₁⁻¹ ∈ LocalGroup E e := (LocalGroup E e).inv_mem (Subgroup.subset_closure hf₁)
  have := (LocalGroup E e).mul_mem h2 h1
  rwa [inv_mul_cancel_left] at this

include hP he hcent hcomm hmem hS hne in
theorem localGroup_eq_centralizer : LocalGroup E e = Subgroup.centralizer ({e} : Set X) := by
  refine le_antisymm localGroup_le_centralizer fun c hc => ?_
  have hM := le_localGroup hP he hcomm hmem hne
  rcases hcent c hc with h | h
  · exact hM h
  · have := (LocalGroup E e).mul_mem (hM h)
      ((LocalGroup E e).inv_mem (mem_localGroup_self hP he hcomm hmem hne))
    rwa [mul_inv_cancel_right] at this

include hP he hcent hcomm hmem hS hZ hne in
theorem val_mem_center_localGroup {z : LocalGroup E e}
    (hz : z ∈ Subgroup.center (LocalGroup E e)) : (z : X) = 1 ∨ (z : X) = e := by
  have hM := le_localGroup hP he hcomm hmem hne
  have he2 : e * e = 1 := Pair.mul_self hP he
  have hzc : (z : X) ∈ Subgroup.centralizer ({e} : Set X) := localGroup_le_centralizer z.2
  have key : ∀ m ∈ M, (∀ g ∈ LocalGroup E e, m * g = g * m) → m = 1 := by
    intro m hm hcm
    have : (⟨m, hm⟩ : M) ∈ Subgroup.center M := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcm g (hM g.2)).symm
    rw [hZ, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hzcomm : ∀ g ∈ LocalGroup E e, (z : X) * g = g * z := fun g hg =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)).symm
  have hecomm : ∀ g ∈ LocalGroup E e, e * g = g * e := fun g hg =>
    (Subgroup.mem_centralizer_singleton_iff.1 (localGroup_le_centralizer hg)).symm
  rcases hcent _ hzc with h | h
  · exact Or.inl (key _ h hzcomm)
  · right
    have h1 : (z : X) * e = 1 := key _ h fun g hg => by
      rw [mul_assoc, hecomm g hg, ← mul_assoc, hzcomm g hg, mul_assoc]
    calc (z : X) = (z : X) * e * e := by rw [mul_assoc, he2, mul_one]
      _ = e := by rw [h1, one_mul]

include hP he hcent hcomm heM hmem hS hZ hne in
theorem exists_localQuotientEquiv :
    ∃ φ : LocalQuotient E e ≃* M,
      (fun q => ((φ q : M) : X)) '' LocalImages E e = (fun f => f * e) '' LocalClass E e := by
  have hM := le_localGroup hP he hcomm hmem hne
  have heG := mem_localGroup_self hP he hcomm hmem hne
  have hG := localGroup_eq_centralizer hP he hcent hcomm hmem hne
  have heZ : (⟨e, heG⟩ : LocalGroup E e) ∈ Subgroup.center (LocalGroup E e) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have : (g : X) ∈ Subgroup.centralizer ({e} : Set X) := hG ▸ g.2
    exact Subgroup.mem_centralizer_singleton_iff.1 this
  let ι : M →* LocalQuotient E e :=
    (QuotientGroup.mk' (Subgroup.center (LocalGroup E e))).comp (Subgroup.inclusion hM)
  have hι : ∀ m : M, ι m = QuotientGroup.mk ⟨m, hM m.2⟩ := fun _ => rfl
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro m hm
    rw [hι, QuotientGroup.eq_one_iff] at hm
    rcases val_mem_center_localGroup hP he hcent hcomm hmem hZ hne hm with h | h
    · exact Subtype.ext h
    · exfalso
      apply heM
      have h' : (m : X) = e := h
      rw [← h']
      exact m.2
  have hsurj : Function.Surjective ι := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hgc : (g : X) ∈ Subgroup.centralizer ({e} : Set X) := hG ▸ g.2
    rcases hcent _ hgc with h | h
    · exact ⟨⟨g, h⟩, by rw [hι]⟩
    · refine ⟨⟨_, h⟩, ?_⟩
      show (QuotientGroup.mk (⟨(g : X) * e, hM h⟩ : LocalGroup E e) : LocalQuotient E e) =
        QuotientGroup.mk g
      rw [show (⟨(g : X) * e, hM h⟩ : LocalGroup E e) = g * ⟨e, heG⟩ from rfl,
        QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 heZ, mul_one]
  let φ : LocalQuotient E e ≃* M := (MulEquiv.ofBijective ι ⟨hinj, hsurj⟩).symm
  have hφ : ∀ (x : X) (hx : x ∈ M), φ (QuotientGroup.mk ⟨x, hM hx⟩) = ⟨x, hx⟩ := fun x hx =>
    (MulEquiv.ofBijective ι ⟨hinj, hsurj⟩).symm_apply_apply ⟨x, hx⟩
  refine ⟨φ, ?_⟩
  ext x
  constructor
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨(f : X), hf, ?_⟩
    have h1 : (QuotientGroup.mk f : LocalQuotient E e) =
        QuotientGroup.mk ⟨(f : X) * e, hM (hmem (f : X) hf)⟩ := by
      rw [show (⟨(f : X) * e, hM (hmem (f : X) hf)⟩ : LocalGroup E e) = f * ⟨e, heG⟩ from rfl,
        QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 heZ, mul_one]
    show (f : X) * e = ((φ (QuotientGroup.mk f) : M) : X)
    rw [h1, hφ _ (hmem (f : X) hf)]
  · rintro ⟨f, hf, rfl⟩
    have hfG : f ∈ LocalGroup E e := Subgroup.subset_closure hf
    refine ⟨QuotientGroup.mk ⟨f, hfG⟩, ⟨⟨f, hfG⟩, hf, rfl⟩, ?_⟩
    have h1 : (QuotientGroup.mk ⟨f, hfG⟩ : LocalQuotient E e) =
        QuotientGroup.mk ⟨f * e, hM (hmem f hf)⟩ := by
      rw [show (⟨f * e, hM (hmem f hf)⟩ : LocalGroup E e) = ⟨f, hfG⟩ * ⟨e, heG⟩ from rfl,
        QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 heZ, mul_one]
    show ((φ (QuotientGroup.mk ⟨f, hfG⟩) : M) : X) = f * e
    rw [h1, hφ _ (hmem f hf)]

end CFSG.Fischer
