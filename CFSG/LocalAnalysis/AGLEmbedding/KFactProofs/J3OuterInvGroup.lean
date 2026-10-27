module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.AGLEmbedding.KFactProofs.J3OuterInv

section Elem

variable {J : Type*} [Group J]

theorem exists_elem_mul {A B : Subgroup J} (hA : IsMulCommutative A) (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hB : IsMulCommutative B) (hB3 : ∀ b ∈ B, b ^ 3 = 1)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hdisj : Disjoint A B) :
    ∃ W : Subgroup J, IsMulCommutative W ∧ (∀ w ∈ W, w ^ 3 = 1) ∧
      Nat.card W = Nat.card A * Nat.card B := by
  have hcomm' : ∀ (m : A) (n : B), Commute (A.subtype m) (B.subtype n) := fun m n =>
    hcomm m.1 m.2 n.1 n.2
  let φ := MonoidHom.noncommCoprod A.subtype B.subtype hcomm'
  have hinj : Function.Injective φ := by
    rw [MonoidHom.noncommCoprod_injective]
    exact ⟨Subtype.val_injective, Subtype.val_injective, by
      simpa [Subgroup.range_subtype] using hdisj⟩
  have hdesc : ∀ x ∈ φ.range, ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    exact ⟨a, a.2, b, b.2, by simp [φ]⟩
  have hc : ∀ a₁ ∈ A, ∀ b₁ ∈ B, ∀ a₂ ∈ A, ∀ b₂ ∈ B,
      Commute (a₁ * b₁) (a₂ * b₂) := by
    intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂
    have h1 : Commute a₁ a₂ := congrArg Subtype.val
      (mul_comm' (⟨a₁, ha₁⟩ : A) ⟨a₂, ha₂⟩)
    have h2 : Commute b₁ b₂ := congrArg Subtype.val
      (mul_comm' (⟨b₁, hb₁⟩ : B) ⟨b₂, hb₂⟩)
    exact Commute.mul_left (Commute.mul_right h1 (hcomm a₁ ha₁ b₂ hb₂))
      (Commute.mul_right (hcomm a₂ ha₂ b₁ hb₁).symm h2)
  refine ⟨φ.range, ⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_, ?_⟩
  · obtain ⟨a₁, ha₁, b₁, hb₁, hx⟩ := hdesc x.1 x.2
    obtain ⟨a₂, ha₂, b₂, hb₂, hy⟩ := hdesc y.1 y.2
    apply Subtype.ext
    change (x : J) * y = y * x
    rw [hx, hy]
    exact (hc a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂).eq
  · obtain ⟨a, ha, b, hb, rfl⟩ := hdesc x hx
    rw [(show Commute a b from hcomm a ha b hb).mul_pow, hA3 a ha, hB3 b hb, one_mul]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod]

theorem false_of_le_zpowers {f : J} {E : Subgroup J} (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hE9 : Nat.card E = 9) (hle : E ≤ Subgroup.zpowers f) : False := by
  have : IsCyclic (E.subgroupOf (Subgroup.zpowers f)) := inferInstance
  have hcyc : IsCyclic E :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hle).surjective
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have h3 : g ^ 3 = 1 := Subtype.ext (hE3 g g.2)
  have := orderOf_dvd_of_pow_eq_one h3
  rw [hg, hE9] at this
  omega

end Elem

section Induced

variable {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [FaithfulSMul G Ω]

theorem exists_induced_aut {a b a' b' : G} (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (σ : Equiv.Perm Ω) (ha : σ * MulAction.toPermHom G Ω a = MulAction.toPermHom G Ω a' * σ)
    (hb : σ * MulAction.toPermHom G Ω b = MulAction.toPermHom G Ω b' * σ) :
    ∃ φ : MulAut G, ∀ x, MulAction.toPermHom G Ω (φ x) =
      σ * MulAction.toPermHom G Ω x * σ⁻¹ := by
  set ψ := MulAction.toPermHom G Ω with hψ
  have hinj : Function.Injective ψ := MulAction.toPerm_injective
  let S : Subgroup G := ψ.range.comap ((MulAut.conj σ).toMonoidHom.comp ψ)
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨a', by
        change ψ a' = σ * ψ x * σ⁻¹
        rw [ha, mul_inv_cancel_right]⟩
    · exact ⟨b', by
        change ψ b' = σ * ψ x * σ⁻¹
        rw [hb, mul_inv_cancel_right]⟩
  have hex : ∀ x : G, ∃ y : G, ψ y = σ * ψ x * σ⁻¹ := fun x => by
    obtain ⟨y, hy⟩ := (hS ▸ Subgroup.mem_top x : x ∈ S)
    exact ⟨y, hy⟩
  choose f hf using hex
  have hmul : ∀ x y, f (x * y) = f x * f y := fun x y => hinj (by
    rw [hf, map_mul, map_mul, hf, hf]
    group)
  have hfinj : Function.Injective f := fun x y h => hinj (by
    have h1 : σ * ψ x * σ⁻¹ = σ * ψ y * σ⁻¹ := by rw [← hf, ← hf, h]
    simpa using h1)
  let F : G →* G := MonoidHom.mk' f hmul
  have hbij : Function.Bijective F := ⟨hfinj, Finite.injective_iff_surjective.1 hfinj⟩
  exact ⟨MulEquiv.ofBijective F hbij, hf⟩

end Induced

section Main

variable {J : Type*} [Group J] [Finite J]

structure OuterSetup (J : Type*) [Group J] (T Z : Subgroup J) (φ : MulAut J) : Prop where
  cen : ∀ z : J, (∀ x, x * z = z * x) → z = 1
  overgroup : ∀ K : Subgroup J, T ≤ K → K ≤ Subgroup.normalizer (T : Set J) ∨ K = ⊤
  Zc : ∀ z ∈ Z, ∀ x ∈ T, x * z = z * x
  Zcomm : IsMulCommutative Z
  Z3 : ∀ z ∈ Z, z ^ 3 = 1
  Z9 : Nat.card Z = 9
  rank : ¬ ∃ W : Subgroup J, IsMulCommutative W ∧ (∀ w ∈ W, w ^ 3 = 1) ∧ Nat.card W = 81
  cent : ∀ z ∈ Z, z ≠ 1 → Subgroup.centralizer {z} ≤ Subgroup.normalizer (T : Set J) →
    Subgroup.centralizer {z} ≤ T
  out : ∀ β γ : MulAut J, β ∉ (MulAut.conj : J →* MulAut J).range →
    γ ∉ (MulAut.conj : J →* MulAut J).range →
      β * γ⁻¹ ∈ (MulAut.conj : J →* MulAut J).range
  phiT : ∀ x ∈ T, φ x ∈ T
  phiOut : φ ∉ (MulAut.conj : J →* MulAut J).range
  final : ∀ g ∈ Subgroup.normalizer (T : Set J), (MulAut.conj g * φ) ^ 2 = 1 →
    ∀ E : Subgroup J, E ≤ T → IsMulCommutative E → (∀ x ∈ E, x ^ 3 = 1) → Nat.card E = 9 →
      ∃ x ∈ E, (MulAut.conj g * φ) x ≠ x

theorem no_fixed_of_le {T Z : Subgroup J} {φ : MulAut J} (H : OuterSetup J T Z φ)
    {α : MulAut J} (hα2 : α ^ 2 = 1) (hαout : α ∉ (MulAut.conj : J →* MulAut J).range)
    {E : Subgroup J} (hET : E ≤ T) (hE : IsMulCommutative E) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hE9 : Nat.card E = 9) : ∃ x ∈ E, α x ≠ x := by
  by_contra hfix
  push Not at hfix
  obtain ⟨z, hzE, hzZ, hz1⟩ : ∃ z ∈ E, z ∈ Z ∧ z ≠ 1 := by
    by_contra hno
    push Not at hno
    obtain ⟨W, hW, hW3, hWc⟩ := exists_elem_mul hE hE3 H.Zcomm H.Z3
      (fun a ha b hb => H.Zc b hb a (hET ha))
      (Subgroup.disjoint_def.2 fun {x} hxE hxZ => hno x hxE hxZ)
    exact H.rank ⟨W, hW, hW3, by rw [hWc, hE9, H.Z9]⟩
  have hTC : T ≤ Subgroup.centralizer {z} := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (H.Zc z hzZ x hx)
  have hCT : Subgroup.centralizer {z} ≤ T := by
    rcases H.overgroup _ hTC with hCN | hCtop
    · exact H.cent z hzZ hz1 hCN
    · exact absurd (H.cen z fun x => Subgroup.mem_centralizer_singleton_iff.1
        (hCtop ▸ Subgroup.mem_top x)) hz1
  have hαT : ∀ x ∈ T, α x ∈ T := by
    intro x hx
    apply hCT
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have hαz : α z = z := hfix z hzE
    have h1 : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.1 (hTC hx)
    calc α x * z = α x * α z := by rw [hαz]
      _ = α (x * z) := (map_mul α x z).symm
      _ = α (z * x) := by rw [h1]
      _ = α z * α x := map_mul α z x
      _ = z * α x := by rw [hαz]
  have hφ' : ∀ x ∈ T, φ⁻¹ x ∈ T := by
    intro x hx
    let f : T → T := fun y => ⟨φ y, H.phiT y y.2⟩
    have hf : Function.Injective f := fun y₁ y₂ h =>
      Subtype.ext (φ.injective (congrArg Subtype.val h))
    obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.1 hf ⟨x, hx⟩
    have hφy : φ y = x := congrArg Subtype.val hy
    have : φ⁻¹ x = y := by rw [← hφy]; exact φ.symm_apply_apply y
    rw [this]
    exact y.2
  obtain ⟨g, hg⟩ := H.out α φ hαout H.phiOut
  have hαeq : α = MulAut.conj g * φ := by rw [hg]; group
  have hgN : g ∈ Subgroup.normalizer (T : Set J) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have : g * x * g⁻¹ = α (φ⁻¹ x) := by
      have := congrArg (fun β : MulAut J => β x) hg
      simpa [MulAut.conj_apply] using this
    rw [this]
    exact hαT _ (hφ' x hx)
  subst hαeq
  obtain ⟨x, hx, hne⟩ := H.final g hgN hα2 E hET hE hE3 hE9
  exact hne (hfix x hx)

theorem no_fixed_elem {S : Sylow 3 J} {Z : Subgroup J} {φ : MulAut J}
    (H : OuterSetup J (S : Subgroup J) Z φ) {α : MulAut J} (hα2 : α ^ 2 = 1)
    (hαout : α ∉ (MulAut.conj : J →* MulAut J).range) {E : Subgroup J}
    (hE : IsMulCommutative E) (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hE9 : Nat.card E = 9) :
    ∃ x ∈ E, α x ≠ x := by
  by_contra hfix
  push Not at hfix
  have hEp : IsPGroup 3 E := fun x => ⟨1, by simpa using Subtype.ext (hE3 x x.2)⟩
  obtain ⟨S', hS'⟩ := hEp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq J S' S
  have hSc : (S : Subgroup J) = (S' : Subgroup J).map (MulAut.conj c).toMonoidHom := by
    have h2 : ((c • S' : Sylow 3 J) : Subgroup J) =
        (S' : Subgroup J).map (MulAut.conj c).toMonoidHom := by
      rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
      rfl
    rw [hc] at h2
    exact h2
  have hcc : ∀ x, (MulAut.conj c) x = c * x * c⁻¹ := fun x => rfl
  set E' := E.map (MulAut.conj c).toMonoidHom with hE'
  have hE'S : E' ≤ (S : Subgroup J) := hSc ▸ Subgroup.map_mono hS'
  set α' : MulAut J := MulAut.conj c * α * MulAut.conj c⁻¹ with hα'
  have hα'x : ∀ x, α' x = c * α (c⁻¹ * x * c) * c⁻¹ := fun x => by
    simp [hα', MulAut.conj_apply]
  have hα2x : ∀ x, α (α x) = x := fun x => by
    have := congrArg (fun β : MulAut J => β x) hα2
    simpa [pow_two] using this
  have hα'2 : α' ^ 2 = 1 := by
    ext x
    simp only [pow_two, MulAut.mul_apply, MulAut.one_apply, hα'x]
    have : c⁻¹ * (c * α (c⁻¹ * x * c) * c⁻¹) * c = α (c⁻¹ * x * c) := by group
    rw [this, hα2x]
    group
  have hα'out : α' ∉ (MulAut.conj : J →* MulAut J).range := by
    rintro ⟨d, hd⟩
    refine hαout ⟨c⁻¹ * d * c, ?_⟩
    ext x
    have h1 : d * (c * x * c⁻¹) * d⁻¹ = c * α x * c⁻¹ := by
      have := congrArg (fun β : MulAut J => β (c * x * c⁻¹)) hd
      simp only [MulAut.conj_apply, hα'x] at this
      rwa [show c⁻¹ * (c * x * c⁻¹) * c = x by group] at this
    show c⁻¹ * d * c * x * (c⁻¹ * d * c)⁻¹ = α x
    calc c⁻¹ * d * c * x * (c⁻¹ * d * c)⁻¹ = c⁻¹ * (d * (c * x * c⁻¹) * d⁻¹) * c := by group
      _ = c⁻¹ * (c * α x * c⁻¹) * c := by rw [h1]
      _ = α x := by group
  have := hE
  obtain ⟨x', hx'E, hx'⟩ := no_fixed_of_le H hα'2 hα'out hE'S inferInstance
    (fun y hy => by
      obtain ⟨e, he, rfl⟩ := hy
      change (c * e * c⁻¹) ^ 3 = 1
      rw [conj_pow, hE3 e he]
      group)
    (by rw [hE', Subgroup.card_map_of_injective (MulAut.conj c).injective, hE9])
  obtain ⟨e, he, rfl⟩ := hx'E
  apply hx'
  rw [hα'x]
  show c * α (c⁻¹ * (c * e * c⁻¹) * c) * c⁻¹ = c * e * c⁻¹
  rw [show c⁻¹ * (c * e * c⁻¹) * c = e by group, hfix e he]

end Main

end CFSG.AGLEmbedding.KFactProofs.J3OuterInv
