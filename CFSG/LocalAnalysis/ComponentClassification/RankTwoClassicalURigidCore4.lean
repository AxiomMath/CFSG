module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidQuot4
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidSemiRep
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidL4
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidTorus4

public section

namespace CFSG.ComponentClassification.RankTwoClassical.URigid

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section Helpers

variable {G : Type} [Group G] [Finite G]

theorem map_perfectCore_conj {H : Subgroup G} {a : G}
    (hH : H.map (MulAut.conj a).toMonoidHom = H) :
    (perfectCore H).map (MulAut.conj a).toMonoidHom = perfectCore H := by
  rw [CFSG.Quasithin.map_perfectCore, hH]

theorem map_conj_inf_centralizer {A : Subgroup G} {p a : G} (haA : a ∈ normalizer (A : Set G))
    (hap : a ∈ centralizer ({p} : Set G)) :
    (A ⊓ centralizer ({p} : Set G)).map (MulAut.conj a).toMonoidHom =
      A ⊓ centralizer ({p} : Set G) := by
  refine Subgroup.eq_of_le_of_card_ge ?_
    (Subgroup.card_map_of_injective (MulAut.conj a).injective).ge
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨hyA, hyp⟩ := Subgroup.mem_inf.mp hy
  rw [mem_centralizer_singleton_iff] at hyp hap
  refine Subgroup.mem_inf.mpr ⟨(mem_normalizer_iff.mp haA y).mp hyA, ?_⟩
  rw [mem_centralizer_singleton_iff]
  change a * y * a⁻¹ * p = p * (a * y * a⁻¹)
  have h1 : a⁻¹ * p = p * a⁻¹ := by
    calc a⁻¹ * p = a⁻¹ * (p * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * p) * a⁻¹ := by rw [hap]
      _ = p * a⁻¹ := by group
  calc a * y * a⁻¹ * p = a * y * (a⁻¹ * p) := by group
    _ = a * (y * p) * a⁻¹ := by rw [h1]; group
    _ = a * (p * y) * a⁻¹ := by rw [hyp]
    _ = (a * p) * y * a⁻¹ := by group
    _ = p * (a * y * a⁻¹) := by rw [hap]; group

theorem conj_mem_perfectCore {A : Subgroup G} {p a : G} (haA : a ∈ normalizer (A : Set G))
    (hap : a ∈ centralizer ({p} : Set G)) {y : G}
    (hy : y ∈ perfectCore (A ⊓ centralizer ({p} : Set G))) :
    a * y * a⁻¹ ∈ perfectCore (A ⊓ centralizer ({p} : Set G)) := by
  rw [← map_perfectCore_conj (map_conj_inf_centralizer haA hap)]
  exact ⟨y, hy, rfl⟩

end Helpers

section DFacts

variable {K : Type} [Field K] {f : ℕ} (h : UnitaryFieldData 2 f K)
  {G : Type} [Group G] {A : Subgroup G} {θ : ↥A →* StatedProj (StatedSU (2 + 2) (2 ^ f) K)}

include h in
theorem odd_orderOf_of_mem_liftSub_uBarT [Finite G] (hker : θ.ker = center ↥A)
    (hodd : Odd (Nat.card (center ↥A))) {a : G} (ha : a ∈ liftSub θ (uBarT K f)) :
    Odd (orderOf a) := by
  obtain ⟨haA, c, hc⟩ := mem_liftSub.mp ha
  have hc1 : c ^ (2 ^ f + 1) = 1 := Subtype.ext ((mem_rootsOfUnity _ _).mp c.2)
  have h1 : (⟨a, haA⟩ : ↥A) ^ (2 ^ f + 1) ∈ center ↥A := by
    rw [← hker, MonoidHom.mem_ker, map_pow, ← hc]
    simp only [MonoidHom.comp_apply]
    rw [← map_pow, ← map_pow, hc1, map_one, map_one]
  have h2 : (⟨a, haA⟩ : ↥A) ^ ((2 ^ f + 1) * Nat.card (center ↥A)) = 1 := by
    rw [pow_mul]
    have h3 := pow_card_eq_one' (G := center ↥A) (x := ⟨_, h1⟩)
    exact congrArg Subtype.val h3
  have h3 : orderOf (⟨a, haA⟩ : ↥A) ∣ (2 ^ f + 1) * Nat.card (center ↥A) :=
    orderOf_dvd_of_pow_eq_one h2
  have hodd' : Odd ((2 ^ f + 1) * Nat.card (center ↥A)) :=
    ((Nat.even_pow.mpr ⟨even_two, by
      have := h.one_le
      omega⟩).add_one).mul hodd
  rw [← Subgroup.orderOf_mk a haA]
  exact Odd.of_dvd_nat hodd' h3

theorem liftSub_uBarT_le_centralizer (hker : θ.ker = center ↥A)
    (hW : ⁅uLeviW θ, uLeviW θ⁆ = uLeviW θ) :
    liftSub θ (uBarT K f) ≤ centralizer (uLeviW θ : Set G) := by
  intro a ha
  obtain ⟨haA, hθa⟩ := mem_liftSub.mp ha
  exact mem_centralizer_of_theta_commute hker levLift_le hW (a := ⟨a, haA⟩) fun y hy =>
    uBarT_commute_uBarW hθa (theta_mem_of_mem_levLift hy)

theorem liftSub_uBarT_le_centralizer_p (hker : θ.ker = center ↥A)
    (hodd : Odd (Nat.card (center ↥A))) {p : G} (hpA : p ∈ A) (hp2 : p ^ 2 = 1)
    (hpL : θ ⟨p, hpA⟩ ∈ uBarL K 2 f) :
    liftSub θ (uBarT K f) ≤ centralizer ({p} : Set G) := by
  intro a ha
  obtain ⟨haA, hθa⟩ := mem_liftSub.mp ha
  have hx2 : (⟨p, hpA⟩ : ↥A) ^ 2 = 1 := Subtype.ext (by simpa using hp2)
  have h1 := commute_of_theta_commute hker hodd hx2 (uBarT_commute_uBarL hθa hpL)
  rw [mem_centralizer_singleton_iff]
  exact congrArg Subtype.val h1

end DFacts

section Conj4

variable {K : Type} [Field K] [CharP K 2] [Finite K] {f : ℕ} (h : UnitaryFieldData 2 f K)

theorem exists_map_stdW_eq_conj_two (hf : 2 ≤ f)
    (hW : ⁅stdW (ε := 2) h, stdW (ε := 2) h⁆ = stdW (ε := 2) h) (β : MulAut (stabE (ε := 2) h))
    {R : Matrix (Fin (2 * 1 + 2)) (HypIndex 1 2) K} (hR : IsHypTransport h R)
    {α : MulAut (StatedProj (StatedSU (2 + 2) (2 ^ f) K))} {δ : MulAut (stabE (ε := 2) h)}
    (hαδ : ∀ g, psiU h hR (δ g) = α (psiU h hR g))
    (hδW : ∀ g ∈ (stdW h).map β.toMonoidHom, δ g = g)
    (hfix : ∀ x ∈ (zBlockHom (ε := 2) h).ker, avec h (δ x) = avec h x → avec h x = 0) :
    ∃ g₀ : stabE (ε := 2) h,
      (stdW h).map β.toMonoidHom = (stdW h).map (MulAut.conj g₀).toMonoidHom := by
  obtain ⟨τ, Z, Z', hZZ, hZZ', hδ⟩ := exists_semi_of_psiU h hR (le_refl 2) hαδ
  obtain ⟨hδg, hZe, hZf, hZf0⟩ := semi_eq_of_tvSub h hZZ hZZ' hδ (map_tvSub h hf (le_refl 2) δ)
  have hinj := semi_hinj h hf (le_refl 2) hZZ' hδg hZe hZf0 hfix
  have hZH : ∀ g ∈ (stdW h).map β.toMonoidHom, Z * (smat h g).map τ = smat h g * Z := by
    intro g hg
    have e := hδg g
    rw [hδW g hg] at e
    calc Z * (smat h g).map τ = Z * (smat h g).map τ * (Z' * Z) := by rw [hZZ', Matrix.mul_one]
      _ = smat h g * Z := by rw [← Matrix.mul_assoc, ← e]
  obtain ⟨x₀, -, hx₀H⟩ := exists_mem_ker_avec_conj_eq_zero h hZe hZf hZH hinj
  have hHperf : ⁅(stdW (ε := 2) h).map β.toMonoidHom, (stdW (ε := 2) h).map β.toMonoidHom⁆ =
      (stdW (ε := 2) h).map β.toMonoidHom := by
    rw [← Subgroup.map_commutator, hW]
  set H₂ := ((stdW (ε := 2) h).map β.toMonoidHom).map (MulAut.conj x₀⁻¹).toMonoidHom
  have hH₂perf : ⁅H₂, H₂⁆ = H₂ := by rw [← Subgroup.map_commutator, hHperf]
  have hH₂a : ∀ w ∈ H₂, avec h w = 0 := by
    rintro _ ⟨g, hg, rfl⟩
    simpa [MulAut.conj_apply] using hx₀H g hg
  refine ⟨x₀, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · intro g hg
    have h1 : x₀⁻¹ * g * x₀ ∈ stdW h :=
      mem_stdW_of_avec_eq_zero h hH₂perf hH₂a ⟨g, hg, by simp⟩
    refine ⟨x₀⁻¹ * g * x₀, h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rw [Subgroup.card_map_of_injective (MulAut.conj x₀).injective,
      Subgroup.card_map_of_injective β.injective]

end Conj4

section Tconj

variable {K : Type} [Field K] [CharP K 2] {f : ℕ} (h : UnitaryFieldData 2 f K)
  {G : Type} [Group G] [Finite G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedSU (2 + 2) (2 ^ f) K)} {s : K} (hs : s + h.bar s = 1)
  {p : G} {Θ : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* stabE (ε := 2) h}
  (hΘ : ∀ x, psiU h (isHypTransport_uFrame h (le_refl 2) hs) (Θ x) =
    θ (Subgroup.inclusion (perfectCore_inf_le A p) x))
include hΘ

theorem theta_conj_eq_tconj {a : G} (haA : a ∈ A) (hap : a ∈ centralizer ({p} : Set G))
    {c : rootsOfUnity (2 ^ f + 1) K} (hθa : θ ⟨a, haA⟩ = uProj K (2 + 2) f (torusU K f c))
    (y : ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))) :
    Θ ⟨a * y * a⁻¹, conj_mem_perfectCore (Subgroup.le_normalizer haA) hap y.2⟩ =
      tconj h (le_refl 2) hs c (Θ y) := by
  apply psiU_injective h (isHypTransport_uFrame h (le_refl 2) hs)
  rw [hΘ, psiU_apply]
  change _ = uProj K (2 + 2) f (hypTransport h (isHypTransport_uFrame h (le_refl 2) hs)
    (hdc h (le_refl 2) hs c * (Θ y : hypSU h 1 2) * (hdc h (le_refl 2) hs c)⁻¹))
  simp only [map_mul, map_inv, hypTransport_hdc]
  rw [← hθa, ← psiU_apply, hΘ, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg θ (Subtype.ext rfl)

end Tconj

section Main

variable {K : Type} [Field K] [CharP K 2] [Finite K] {f : ℕ} (h : UnitaryFieldData 2 f K)
  {G : Type} [Group G] [Finite G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedSU (2 + 2) (2 ^ f) K)}

omit [Finite K] [Finite G] in
theorem map_theta_rightConjugate_eq {s : K} (hs : s + h.bar s = 1) {p : G}
    {Θ : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* stabE (ε := 2) h}
    (hΘ : ∀ x, psiU h (isHypTransport_uFrame h (le_refl 2) hs) (Θ x) =
      θ (Subgroup.inclusion (perfectCore_inf_le A p) x))
    {W : Subgroup G} (hWX : W ≤ perfectCore (A ⊓ centralizer ({p} : Set G)))
    (hWstd : (W.subgroupOf (perfectCore (A ⊓ centralizer ({p} : Set G)))).map Θ = stdW h)
    (hWsurj : ∀ u ∈ uBarW K 2 f, ∃ w, ∃ hw : w ∈ W,
      θ ⟨w, perfectCore_inf_le A p (hWX hw)⟩ = u)
    {x : G} (hXx : rightConjugate (perfectCore (A ⊓ centralizer ({p} : Set G))) x =
      perfectCore (A ⊓ centralizer ({p} : Set G)))
    {β : MulAut (stabE (ε := 2) h)} (hβ : ∀ y, β (Θ y) = Θ (conjAut hXx y))
    {g₀ : stabE (ε := 2) h}
    (hg₀ : (stdW h).map β.toMonoidHom = (stdW h).map (MulAut.conj g₀).toMonoidHom) :
    ((rightConjugate W x).subgroupOf A).map θ = (uBarW K 2 f).map
      (MulAut.conj (psiU h (isHypTransport_uFrame h (le_refl 2) hs) g₀)).toMonoidHom := by
  set ψ := psiU h (isHypTransport_uFrame h (le_refl 2) hs)
  have hXA := perfectCore_inf_le A p
  have hWxX : rightConjugate W x ≤ perfectCore (A ⊓ centralizer ({p} : Set G)) :=
    (Subgroup.map_mono hWX).trans hXx.le
  have hγw : ∀ w (hw : w ∈ W), conjAut hXx ⟨w, hWX hw⟩ =
      ⟨x⁻¹ * w * x, hWxX ⟨w, hw, by simp⟩⟩ := fun w hw =>
    Subtype.ext (coe_conjAut hXx _)
  have hA' : ∀ y (hy : y ∈ rightConjugate W x),
      Θ ⟨y, hWxX hy⟩ ∈ (stdW h).map β.toMonoidHom := by
    rintro _ ⟨w, hw, rfl⟩
    have h2 : (⟨(MulAut.conj x⁻¹).toMonoidHom w, hWxX ⟨w, hw, rfl⟩⟩ :
        ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))) =
          ⟨x⁻¹ * w * x, hWxX ⟨w, hw, by simp⟩⟩ := Subtype.ext (by simp)
    rw [h2, ← hγw w hw, ← hβ]
    refine ⟨Θ ⟨w, hWX hw⟩, ?_, rfl⟩
    rw [← hWstd]
    exact ⟨⟨w, hWX hw⟩, hw, rfl⟩
  have hB' : ∀ g ∈ (stdW h).map β.toMonoidHom,
      ∃ y, ∃ hy : y ∈ rightConjugate W x, Θ ⟨y, hWxX hy⟩ = g := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← hWstd] at hg
    obtain ⟨⟨w, hwX⟩, hw, rfl⟩ := hg
    refine ⟨x⁻¹ * w * x, ⟨w, hw, by simp⟩, ?_⟩
    change _ = β (Θ ⟨w, hwX⟩)
    rw [hβ]
    exact congrArg Θ (hγw w hw).symm
  have hψconj : ∀ g : stabE (ε := 2) h, ψ ((MulAut.conj g₀).toMonoidHom g) =
      (MulAut.conj (ψ g₀)).toMonoidHom (ψ g) := fun g => by
    simp [MulAut.conj_apply]
  have hWs : ∀ g ∈ stdW (ε := 2) h, ψ g ∈ uBarW K 2 f := fun g hg => by
    rw [psiU_apply]
    exact (mem_stdW_iff_uBarW h (le_refl 2) hs g).mp hg
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    have h1 := hA' a ha
    rw [hg₀] at h1
    obtain ⟨s', hs', hs'e⟩ := h1
    refine ⟨ψ s', hWs s' hs', ?_⟩
    have e1 : θ a = ψ (Θ ⟨a, hWxX ha⟩) := by
      rw [hΘ]
      rfl
    rw [e1, ← hs'e, hψconj]
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨w, hw, hwu⟩ := hWsurj u hu
    have hs₀ : Θ ⟨w, hWX hw⟩ ∈ stdW h := by
      rw [← hWstd]
      exact ⟨⟨w, hWX hw⟩, hw, rfl⟩
    have hψs₀ : ψ (Θ ⟨w, hWX hw⟩) = u := by
      rw [hΘ, ← hwu]
      rfl
    have hmem : (MulAut.conj g₀).toMonoidHom (Θ ⟨w, hWX hw⟩) ∈
        (stdW h).map β.toMonoidHom := by
      rw [hg₀]
      exact ⟨_, hs₀, rfl⟩
    obtain ⟨y, hy, hye⟩ := hB' _ hmem
    refine ⟨⟨y, hXA (hWxX hy)⟩, hy, ?_⟩
    have e1 : θ ⟨y, hXA (hWxX hy)⟩ = ψ (Θ ⟨y, hWxX hy⟩) := by
      rw [hΘ]
      rfl
    rw [e1, hye, hψconj, hψs₀]

end Main

section ConjP

variable {K : Type} [Field K] [CharP K 2] {f : ℕ} (h : UnitaryFieldData 2 f K)

include h in
theorem noNormalTwo_of_conj (hf : 2 ≤ f) (y : StatedProj (StatedSU (2 + 2) (2 ^ f) K))
    {M : Subgroup (StatedProj (StatedSU (2 + 2) (2 ^ f) K))}
    (hLM : (uBarL K 2 f).map (MulAut.conj y).toMonoidHom ≤ M)
    (hMW : M ≤ centralizer (((uBarW K 2 f).map (MulAut.conj y).toMonoidHom :
      Subgroup (StatedProj (StatedSU (2 + 2) (2 ^ f) K))) :
        Set (StatedProj (StatedSU (2 + 2) (2 ^ f) K)))) :
    NoNormalTwo M := by
  set M' := M.map (MulAut.conj y⁻¹).toMonoidHom
  have hM : M = M'.map (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.map_map]
    refine (Subgroup.map_id M).symm.trans ?_
    congr 1
    ext z
    simp
  have hLM' : uBarL K 2 f ≤ M' := by
    intro l hl
    refine ⟨y * l * y⁻¹, hLM ⟨l, hl, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hMW' : M' ≤ centralizer (uBarW K 2 f : Set (StatedProj (StatedSU (2 + 2) (2 ^ f) K))) := by
    rintro _ ⟨m, hm, rfl⟩
    rw [mem_centralizer_iff]
    intro w hw
    have h1 := mem_centralizer_iff.mp (hMW hm) (y * w * y⁻¹) ⟨w, hw, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1 ⊢
    calc w * (y⁻¹ * m * y) = y⁻¹ * (y * w * y⁻¹ * m) * y := by group
      _ = y⁻¹ * (m * (y * w * y⁻¹)) * y := by rw [h1]
      _ = y⁻¹ * m * y * w := by group
  rw [hM]
  exact noNormalTwo_map_mulAut (noNormalTwo_of_uBarL_le h hf (le_refl 2) hLM' hMW') _

omit [CharP K 2] in
theorem alpha_pow_eq_one {G : Type} [Group G] {A : Subgroup G}
    {θ : ↥A →* StatedProj (StatedSU (2 + 2) (2 ^ f) K)} (hθ : Function.Surjective θ)
    {γ : MulAut ↥A} {α : MulAut (StatedProj (StatedSU (2 + 2) (2 ^ f) K))}
    (hαγ : ∀ a, α (θ a) = θ (γ a)) {m : ℕ} (hγm : γ ^ m = 1) : α ^ m = 1 := by
  have key : ∀ n : ℕ, ∀ a, (α ^ n) (θ a) = θ ((γ ^ n) a) := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      rw [pow_succ', MulAut.mul_apply, ih, hαγ, pow_succ', MulAut.mul_apply]
  apply MulEquiv.ext
  intro z
  obtain ⟨a, rfl⟩ := hθ z
  rw [key, hγm]
  rfl

end ConjP

end CFSG.ComponentClassification.RankTwoClassical.URigid
