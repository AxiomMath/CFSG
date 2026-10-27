module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinCover

public section

namespace CFSG.QuasithinUnique.Fin257

open scoped commutatorElement Pointwise
open CFSG.Open CFSG.Quasithin

@[expose] def MaxRankModel (M : Type) [Group M] (U R₁ R₂ : Subgroup M) : Prop :=
  ∀ E : Subgroup (MulAut M), (∀ α ∈ E, α * α = 1) → (∀ α ∈ E, ∀ β ∈ E, α * β = β * α) →
    (∀ α ∈ E, ∀ u ∈ U, α u ∈ U) →
    Nat.card E ≤ Nat.card R₁ ∧
      (Nat.card E = Nat.card R₁ →
        E = R₁.map (MulAut.conj : M →* MulAut M) ∨ E = R₂.map (MulAut.conj : M →* MulAut M))

theorem MaxRankModel.symm {M : Type} [Group M] {U R₁ R₂ : Subgroup M}
    (h : MaxRankModel M U R₁ R₂) (hcard : Nat.card R₁ = Nat.card R₂) :
    MaxRankModel M U R₂ R₁ := fun E h2 hc hU => by
  obtain ⟨h1, h3⟩ := h E h2 hc hU
  exact ⟨hcard ▸ h1, fun h4 => (h3 (hcard ▸ h4)).symm⟩

theorem exists_induced_aut_fwd {G : Type} [Group G] {K : Subgroup G} {M : Type} [Group M]
    {π : ↥K →* M} (hπ : Function.Surjective π)
    (hcen : ∀ x : ↥K, (∀ y : ↥K, x * y = y * x) → π x = 1)
    (hker : ∀ x : ↥K, π x = 1 → ∀ y : ↥K, x * y = y * x)
    {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    ∃ α : MulAut M, ∀ (x : ↥K) (hx : g * (x : G) * g⁻¹ ∈ K), α (π x) = π ⟨g * x * g⁻¹, hx⟩ := by
  obtain ⟨α, hα⟩ := exists_induced_aut hπ hcen hker (inv_mem hg)
  refine ⟨α, fun x hx => ?_⟩
  have hx' : (g⁻¹)⁻¹ * (x : G) * g⁻¹ ∈ K := by simpa using hx
  have := hα x hx'
  have e : (⟨(g⁻¹)⁻¹ * x * g⁻¹, hx'⟩ : ↥K) = ⟨g * x * g⁻¹, hx⟩ := Subtype.ext (by simp)
  rw [e] at this
  exact this

section Transfer

variable {G : Type} [Group G] {K P : Subgroup G} {M : Type} [Group M] {U : Subgroup M}
  {π : ↥K →* M}

@[expose] noncomputable def indAut (hπ : Function.Surjective π)
    (hcen : ∀ x : ↥K, (∀ y : ↥K, x * y = y * x) → π x = 1)
    (hker : ∀ x : ↥K, π x = 1 → ∀ y : ↥K, x * y = y * x)
    (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)) : MulAut M :=
  (exists_induced_aut_fwd hπ hcen hker hg).choose

theorem indAut_apply (hπ : Function.Surjective π)
    (hcen : ∀ x : ↥K, (∀ y : ↥K, x * y = y * x) → π x = 1)
    (hker : ∀ x : ↥K, π x = 1 → ∀ y : ↥K, x * y = y * x)
    {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) (x : ↥K)
    (hx : g * (x : G) * g⁻¹ ∈ K) : indAut hπ hcen hker g hg (π x) = π ⟨g * x * g⁻¹, hx⟩ :=
  (exists_induced_aut_fwd hπ hcen hker hg).choose_spec x hx

theorem mem_normalizer_conj {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) (x : ↥K) :
    g * (x : G) * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hg x).mp x.2


variable (hπ : Function.Surjective π)
  (hcen : ∀ x : ↥K, (∀ y : ↥K, x * y = y * x) → π x = 1)
  (hker : ∀ x : ↥K, π x = 1 → ∀ y : ↥K, x * y = y * x)

include hπ hcen hker in
theorem indAut_mul {g h : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hh : h ∈ Subgroup.normalizer (K : Set G)) (hgh : g * h ∈ Subgroup.normalizer (K : Set G)) :
    indAut hπ hcen hker (g * h) hgh = indAut hπ hcen hker g hg * indAut hπ hcen hker h hh := by
  ext y
  obtain ⟨x, rfl⟩ := hπ y
  rw [MulAut.mul_apply, indAut_apply hπ hcen hker hh x (mem_normalizer_conj hh x),
    indAut_apply hπ hcen hker hg ⟨h * x * h⁻¹, mem_normalizer_conj hh x⟩
      (mem_normalizer_conj hg _),
    indAut_apply hπ hcen hker hgh x (mem_normalizer_conj hgh x)]
  congr 1
  apply Subtype.ext
  simp [mul_assoc]

include hπ hcen hker in
theorem indAut_one : indAut hπ hcen hker 1 (one_mem _) = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := hπ y
  rw [indAut_apply hπ hcen hker (one_mem _) x (mem_normalizer_conj (one_mem _) x)]
  simp

@[expose] noncomputable def indHom (A : Subgroup G) (hA : A ≤ Subgroup.normalizer (K : Set G)) :
    ↥A →* MulAut M where
  toFun a := indAut hπ hcen hker a.1 (hA a.2)
  map_one' := indAut_one hπ hcen hker
  map_mul' a b := indAut_mul hπ hcen hker (hA a.2) (hA b.2) (hA (A.mul_mem a.2 b.2))

theorem indHom_apply (A : Subgroup G) (hA : A ≤ Subgroup.normalizer (K : Set G)) (a : ↥A) :
    indHom hπ hcen hker A hA a = indAut hπ hcen hker a.1 (hA a.2) := rfl

theorem mem_centralizer_of_indAut_eq_one {g : G} (hq : CFSG.IsQuasisimple ↥K)
    (hg : g ∈ Subgroup.normalizer (K : Set G))
    (h1 : indAut hπ hcen hker g hg = 1) : g ∈ Subgroup.centralizer (K : Set G) := by
  have hgi : g⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
    refine centralizes_of_acts_trivially (π := π) hq hker (g := g⁻¹) (fun x hx => ?_)
      (fun x hx => ?_)
    · have := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
      simpa using this
    · have := indAut_apply hπ hcen hker hg x (by simpa using hx)
      rw [h1] at this
      have e : (⟨g * x * g⁻¹, by simpa using hx⟩ : ↥K) = ⟨(g⁻¹)⁻¹ * x * g⁻¹, hx⟩ :=
        Subtype.ext (by simp)
      rw [e] at this
      exact this.symm.trans (by simp)
  simpa using inv_mem hgi

theorem indAut_eq_one_of_mem_centralizer {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    (h1 : g ∈ Subgroup.centralizer (K : Set G)) : indAut hπ hcen hker g hg = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := hπ y
  rw [indAut_apply hπ hcen hker hg x (mem_normalizer_conj hg x)]
  have : g * (x : G) * g⁻¹ = x := by
    have := Subgroup.mem_centralizer_iff.mp h1 x x.2
    rw [← this]
    group
  have e : (⟨g * x * g⁻¹, mem_normalizer_conj hg x⟩ : ↥K) = x := Subtype.ext this
  rw [e]
  simp


include hπ hcen hker in
theorem indAut_of_mem (x : ↥K) (hx : (x : G) ∈ Subgroup.normalizer (K : Set G)) :
    indAut hπ hcen hker x hx = MulAut.conj (π x) := by
  ext y
  obtain ⟨z, rfl⟩ := hπ y
  rw [indAut_apply hπ hcen hker hx z (mem_normalizer_conj hx z)]
  have e : (⟨(x : G) * z * (x : G)⁻¹, mem_normalizer_conj hx z⟩ : ↥K) = x * z * x⁻¹ :=
    Subtype.ext (by simp)
  rw [e, map_mul, map_mul, map_inv]
  simp [MulAut.conj_apply]

end Transfer

theorem card_pre {G : Type} [Group G] [Finite G] {K : Subgroup G} {M : Type} [Group M] [Finite M]
    {π : ↥K →* M} (hπ : Function.Surjective π) (R : Subgroup M) :
    Nat.card ↥(pre π R) = Nat.card ↥(pre π (⊥ : Subgroup M)) * Nat.card R := by
  have hc : ∀ S : Subgroup M, Nat.card ↥(pre π S) = Nat.card ↥(S.comap π) := fun S =>
    Subgroup.card_map_of_injective K.subtype_injective
  rw [hc, hc]
  have h1 : ∀ S : Subgroup M, Nat.card ↥(S.comap π) * S.index = Nat.card ↥K := by
    intro S
    rw [← Subgroup.index_comap_of_surjective S hπ]
    exact Subgroup.card_mul_index _
  have h2 : ∀ S : Subgroup M, Nat.card S * S.index = Nat.card M := fun S => Subgroup.card_mul_index S
  have h3 := Subgroup.card_ker_mul_card_of_surjective hπ
  have hpos : 0 < R.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hbot : Nat.card ↥((⊥ : Subgroup M).comap π) = Nat.card π.ker := by
    rw [MonoidHom.comap_bot]
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, hbot, mul_assoc, h2, h3]


theorem pre_inf_centralizer {G : Type} [Group G] {K : Subgroup G} {M : Type} [Group M]
    {π : ↥K →* M} (hcen : ∀ x : ↥K, (∀ y : ↥K, x * y = y * x) → π x = 1)
    (hker : ∀ x : ↥K, π x = 1 → ∀ y : ↥K, x * y = y * x) (R : Subgroup M) :
    pre π R ⊓ Subgroup.centralizer (K : Set G) = pre π (⊥ : Subgroup M) := by
  ext x
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hxR, hxC⟩
    obtain ⟨hxK, -⟩ := mem_pre.mp hxR
    refine mem_pre.mpr ⟨hxK, ?_⟩
    rw [Subgroup.mem_bot]
    apply hcen
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2).symm
  · intro hx
    obtain ⟨hxK, hx1⟩ := mem_pre.mp hx
    rw [Subgroup.mem_bot] at hx1
    refine ⟨mem_pre.mpr ⟨hxK, by rw [hx1]; exact one_mem R⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (hker ⟨x, hxK⟩ hx1 ⟨h, hh⟩).symm

theorem maxRank_of_red {G : Type} [Group G] [Finite G] {K P K₁ K₂ V V' : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥K) {M : Type} [Group M] [Finite M] {U R₁ R₂ : Subgroup M}
    {π : ↥K →* M} (hred : Red257 K P K₁ K₂ V V' π U R₁ R₂)
    (hMR : MaxRankModel M U R₁ R₂) :
    ∀ A : Subgroup G, A ≤ Subgroup.normalizer (K : Set G) → A ≤ Subgroup.normalizer (P : Set G) →
      IsElemAbelian 2 A →
      Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (K : Set G)) ≤
        Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set G)) * Nat.card V ∧
      (Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (K : Set G)) =
          Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set G)) * Nat.card V →
        A ≤ V ⊔ Subgroup.centralizer (K : Set G) ∨ A ≤ V' ⊔ Subgroup.centralizer (K : Set G)) := by
  intro A hAK hAP hAe
  have hπ := hred.surj
  have hcen := hred.center_le
  have hker := hred.ker_central
  set ρ := indHom hπ hcen hker A hAK with hρ
  have hAcomm : ∀ a b : ↥A, a * b = b * a := fun a b => hAe.1.is_comm.comm a b
  have hA2 : ∀ a : ↥A, a * a = 1 := fun a => Subtype.ext (by
    have := hAe.2 a a.2
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
    exact this)
  have hE2 : ∀ α ∈ ρ.range, α * α = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul, hA2, map_one]
  have hEc : ∀ α ∈ ρ.range, ∀ β ∈ ρ.range, α * β = β * α := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, hAcomm]
  have hEU : ∀ α ∈ ρ.range, ∀ u ∈ U, α u ∈ U := by
    rintro _ ⟨a, rfl⟩ u hu
    obtain ⟨x, rfl⟩ := hπ u
    have hxP : (x : G) ∈ P := by
      rw [hred.hP]
      exact mem_pre_of_mem x hu
    have hmem : (a : G) * x * (a : G)⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hAP a.2) x).mp hxP
    rw [hred.hP] at hmem
    obtain ⟨h, hh⟩ := mem_pre.mp hmem
    rw [indHom_apply, indAut_apply hπ hcen hker (hAK a.2) x (mem_normalizer_conj (hAK a.2) x)]
    exact hh
  obtain ⟨hbound, hequal⟩ := hMR ρ.range hE2 hEc hEU
  have hkerρ : ρ.ker = (A ⊓ Subgroup.centralizer (K : Set G)).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      exact ⟨a.2, mem_centralizer_of_indAut_eq_one hπ hcen hker hq (hAK a.2) h⟩
    · intro h
      exact indAut_eq_one_of_mem_centralizer hπ hcen hker (hAK a.2) h.2
  have hAcard : Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set G)) * Nat.card ρ.range =
      Nat.card A := by
    rw [← Subgroup.card_ker_mul_card_range ρ, hkerρ]
    congr 1
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
  have hVcard : Nat.card V = Nat.card ↥(V ⊓ Subgroup.centralizer (K : Set G)) * Nat.card R₁ := by
    rw [hred.hV, pre_inf_centralizer hcen hker, card_pre hπ]
  have hV'card : Nat.card V' =
      Nat.card ↥(V' ⊓ Subgroup.centralizer (K : Set G)) * Nat.card R₂ := by
    rw [hred.hV', pre_inf_centralizer hcen hker, card_pre hπ]
  have hVC : V ⊓ Subgroup.centralizer (K : Set G) = V' ⊓ Subgroup.centralizer (K : Set G) := by
    rw [hred.hV, hred.hV', pre_inf_centralizer hcen hker, pre_inf_centralizer hcen hker]
  have hposC : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer (K : Set G)) := Nat.card_pos
  have hposAC : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set G)) := Nat.card_pos
  refine ⟨?_, fun heq => ?_⟩
  · rw [← hAcard, hVcard]
    calc Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set G)) * Nat.card ρ.range *
          Nat.card ↥(V ⊓ Subgroup.centralizer (K : Set G))
        = (Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set G)) *
          Nat.card ↥(V ⊓ Subgroup.centralizer (K : Set G))) * Nat.card ρ.range := by ring
      _ ≤ (Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set G)) *
          Nat.card ↥(V ⊓ Subgroup.centralizer (K : Set G))) * Nat.card R₁ :=
        Nat.mul_le_mul_left _ hbound
      _ = _ := by ring
  · have hE : Nat.card ρ.range = Nat.card R₁ := by
      rw [← hAcard, hVcard] at heq
      have h1 : (Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set G)) *
          Nat.card ↥(V ⊓ Subgroup.centralizer (K : Set G))) * Nat.card ρ.range =
          (Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set G)) *
          Nat.card ↥(V ⊓ Subgroup.centralizer (K : Set G))) * Nat.card R₁ := by
        calc _ = Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set G)) * Nat.card ρ.range *
              Nat.card ↥(V ⊓ Subgroup.centralizer (K : Set G)) := by ring
          _ = _ := heq
          _ = _ := by ring
      exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hposAC hposC) h1
    have key : ∀ (R : Subgroup M), ρ.range = R.map (MulAut.conj : M →* MulAut M) →
        A ≤ pre π R ⊔ Subgroup.centralizer (K : Set G) := by
      intro R hR a ha
      have hmem : indHom hπ hcen hker A hAK ⟨a, ha⟩ ∈ R.map (MulAut.conj : M →* MulAut M) := by
        rw [← hR]
        exact ⟨⟨a, ha⟩, rfl⟩
      obtain ⟨r, hr, hra⟩ := hmem
      obtain ⟨x, hx⟩ := hπ r
      have hxN : (x : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer x.2
      have hxV : (x : G) ∈ pre π R := mem_pre_of_mem x (by rw [hx]; exact hr)
      have hxa : (x : G)⁻¹ * a ∈ Subgroup.normalizer (K : Set G) :=
        mul_mem (inv_mem hxN) (hAK ha)
      have hinv : (x : G)⁻¹ ∈ Subgroup.normalizer (K : Set G) := inv_mem hxN
      have hind : indAut hπ hcen hker ((x : G)⁻¹ * a) hxa = 1 := by
        have h1 : indAut hπ hcen hker ((x : G)⁻¹ * a) hxa =
            indAut hπ hcen hker ((x : G)⁻¹) hinv * indAut hπ hcen hker a (hAK ha) :=
          indAut_mul hπ hcen hker hinv (hAK ha) hxa
        have h2 : indAut hπ hcen hker ((x : G)⁻¹) hinv = MulAut.conj (π x⁻¹) :=
          indAut_of_mem hπ hcen hker x⁻¹ hinv
        have h3 : indAut hπ hcen hker a (hAK ha) = MulAut.conj r := hra.symm
        rw [h1, h2, h3, map_inv, hx, ← map_mul, inv_mul_cancel, map_one]
      have hC := mem_centralizer_of_indAut_eq_one hπ hcen hker hq hxa hind
      have : a = (x : G) * ((x : G)⁻¹ * a) := by group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left hxV) (Subgroup.mem_sup_right hC)
    rcases hequal hE with h | h
    · left
      rw [hred.hV]
      exact key R₁ h
    · right
      rw [hred.hV']
      exact key R₂ h


theorem conj_injective_of_center {M : Type} [Group M]
    (hM : ∀ m : M, (∀ y : M, m * y = y * m) → m = 1) :
    Function.Injective (MulAut.conj : M →* MulAut M) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  apply hM
  intro y
  have := congrArg (fun φ : MulAut M => φ y) hx
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  calc x * y = (x * y * x⁻¹) * x := by group
    _ = y * x := by rw [this]

theorem comap_conj_le_U {M : Type} [Group M] [Finite M] {U R₁ R₂ : Subgroup M}
    (hM : ModelData M U R₁ R₂) (E : Subgroup (MulAut M)) (h2 : ∀ α ∈ E, α * α = 1)
    (hU : ∀ α ∈ E, ∀ u ∈ U, α u ∈ U) :
    (∀ x ∈ E.comap (MulAut.conj : M →* MulAut M), x * x = 1) ∧
      E.comap (MulAut.conj : M →* MulAut M) ≤ U := by
  have hinj := conj_injective_of_center hM.center_trivial
  have hB2 : ∀ x ∈ E.comap (MulAut.conj : M →* MulAut M), x * x = 1 := by
    intro x hx
    apply hinj
    rw [map_mul, map_one]
    exact h2 _ hx
  refine ⟨hB2, fun x hx => ?_⟩
  have hx' : (MulAut.conj x : MulAut M) ∈ E := hx
  have h1 : ∀ u ∈ U, x * u * x⁻¹ ∈ U := fun u hu => hU _ hx' u hu
  have h1' : ∀ u ∈ U, x⁻¹ * u * x ∈ U := fun u hu => by
    have := hU _ (E.inv_mem hx') u hu
    simpa [MulAut.conj_apply, MulAut.inv_def] using this
  have hxN : x ∈ Subgroup.normalizer (U : Set M) := mem_normalizer_of_conj U h1 h1'
  obtain ⟨r, hr, hxr⟩ := exists_odd_pow_mem hM.sylow x hxN
  obtain ⟨j, hj⟩ := hr
  have : x ^ r = x := by
    rw [hj, pow_succ, pow_mul, pow_two, hB2 x hx, one_pow, one_mul]
  rwa [this] at hxr

theorem fixes_of_comm {M : Type} [Group M] (hinj : Function.Injective (MulAut.conj : M →* MulAut M))
    {θ : MulAut M} {x : M} (hcomm : θ * MulAut.conj x = MulAut.conj x * θ) : θ x = x := by
  apply hinj
  have h1 : MulAut.conj (θ x) = θ * MulAut.conj x * θ⁻¹ := by
    refine MulEquiv.ext fun y => ?_
    simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_def]
  rw [h1, hcomm]
  group

theorem maxRankModel_of_outer {M : Type} [Group M] [Finite M] {U R₁ R₂ : Subgroup M}
    (hM : ModelData M U R₁ R₂) (hcard : Nat.card R₁ = Nat.card R₂)
    (hEA : ∀ B : Subgroup M, B ≤ U → (∀ x ∈ B, x * x = 1) → B ≤ R₁ ∨ B ≤ R₂)
    (houter : ∀ E : Subgroup (MulAut M), (∀ α ∈ E, α * α = 1) →
      (∀ α ∈ E, ∀ β ∈ E, α * β = β * α) → (∀ α ∈ E, ∀ u ∈ U, α u ∈ U) →
      (∃ θ ∈ E, θ ∉ (MulAut.conj : M →* MulAut M).range) → Nat.card E < Nat.card R₁) :
    MaxRankModel M U R₁ R₂ := by
  intro E h2 hc hU
  by_cases hout : ∃ θ ∈ E, θ ∉ (MulAut.conj : M →* MulAut M).range
  · have := houter E h2 hc hU hout
    exact ⟨this.le, fun h => absurd h this.ne⟩
  · push Not at hout
    have hinj := conj_injective_of_center hM.center_trivial
    set B := E.comap (MulAut.conj : M →* MulAut M) with hB
    have hEB : B.map (MulAut.conj : M →* MulAut M) = E := Subgroup.map_comap_eq_self hout
    have hcardE : Nat.card E = Nat.card B := by
      rw [← hEB]
      exact Subgroup.card_map_of_injective hinj
    have hB2 : ∀ x ∈ B, x * x = 1 := by
      intro x hx
      apply hinj
      rw [map_mul, map_one]
      exact h2 _ hx
    have hBN : ∀ x ∈ B, x ∈ Subgroup.normalizer (U : Set M) := by
      intro x hx
      have hx' : (MulAut.conj x : MulAut M) ∈ E := hx
      have h1 : ∀ u ∈ U, x * u * x⁻¹ ∈ U := fun u hu => hU _ hx' u hu
      have h1' : ∀ u ∈ U, x⁻¹ * u * x ∈ U := fun u hu => by
        have := hU _ (E.inv_mem hx') u hu
        simpa [MulAut.conj_apply, MulAut.inv_def] using this
      exact mem_normalizer_of_conj U h1 h1'
    have hBU : B ≤ U := by
      intro x hx
      obtain ⟨r, hr, hxr⟩ := exists_odd_pow_mem hM.sylow x (hBN x hx)
      obtain ⟨j, hj⟩ := hr
      have : x ^ r = x := by
        rw [hj, pow_succ, pow_mul, pow_two, hB2 x hx, one_pow, one_mul]
      rwa [this] at hxr
    rcases hEA B hBU hB2 with h | h
    · refine ⟨?_, fun heq => Or.inl ?_⟩
      · rw [hcardE]
        exact Subgroup.card_le_of_le h
      · have : B = R₁ := Subgroup.eq_of_le_of_card_ge h (by rw [← hcardE, heq])
        rw [← hEB, this]
    · refine ⟨?_, fun heq => Or.inr ?_⟩
      · rw [hcardE, hcard]
        exact Subgroup.card_le_of_le h
      · have : B = R₂ := Subgroup.eq_of_le_of_card_ge h (by rw [← hcardE, heq, hcard])
        rw [← hEB, this]

end CFSG.QuasithinUnique.Fin257
