module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinKL

public section

namespace CFSG.QuasithinUnique.Fin257

open scoped commutatorElement Pointwise
open CFSG.Open CFSG.Quasithin

structure RedP257 {G : Type} [Group G] (K P : Subgroup G) {M : Type} [Group M]
    (π : ↥K →* M) (U : Subgroup M) : Prop where
  surj : Function.Surjective π
  ker_central : ∀ x : ↥K, π x = 1 → ∀ y : ↥K, x * y = y * x
  ker_two : IsPGroup 2 π.ker
  center_le : ∀ x : ↥K, (∀ y : ↥K, x * y = y * x) → π x = 1
  hP : P = pre π U

theorem reduceP {G : Type} [Group G] [Finite G] {K P : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥K) {M : Type} [Group M] [Finite M] {U R₁ R₂ : Subgroup M}
    (hM : ModelData M U R₁ R₂) (e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* M) (hS : IsSylowTwoOf P K) :
    ∃ π : ↥K →* M, RedP257 K P π U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial M := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    exact hM.ne (Subgroup.ext fun x => by simp [Subsingleton.elim x 1])
  set π₀ := quotMap K e with hπ₀def
  have hπ₀ : Function.Surjective π₀ := quotMap_surjective K e
  have hker0 : ∀ x, π₀ x = 1 ↔ x ∈ CFSG.pCore 2 ↥K := quotMap_eq_one_iff K e
  have hcen : ∀ x : ↥K, (∀ y, x * y = y * x) → π₀ x = 1 := fun x hx =>
    center_le_ker hM.center_trivial π₀ hπ₀ x hx
  have hkc : ∀ x : ↥K, π₀ x = 1 → ∀ y, x * y = y * x :=
    ker_central_of_quasisimple hq π₀ hπ₀ hcen
  have hk2 : IsPGroup 2 π₀.ker := by
    have : π₀.ker = CFSG.pCore 2 ↥K := by
      ext x
      exact hker0 x
    rw [this]
    exact CFSG.pCore_isPGroup
  set P' := P.subgroupOf K with hP'def
  have hkerP : ∀ x : ↥K, π₀ x = 1 → x ∈ P' := by
    intro x hx
    have hx' : x ∈ CFSG.pCore 2 ↥K := (hker0 x).mp hx
    have h1 : (x : G) ∈ pCoreOf 2 K := ⟨x, hx', rfl⟩
    exact EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS h1
  have hP2 : IsPGroup 2 P' := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  set S := P'.map π₀ with hSdef
  have hPS : P' = S.comap π₀ := by
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨p, hp, hpx⟩
      have h1 : π₀ (p⁻¹ * x) = 1 := by rw [map_mul, map_inv, hpx, inv_mul_cancel]
      have h2 : p⁻¹ * x ∈ P' := hkerP _ h1
      have h3 : p * (p⁻¹ * x) ∈ P' := P'.mul_mem hp h2
      simpa using h3
  have hSp : IsPGroup 2 S := hP2.map π₀
  have hSi : ¬ 2 ∣ S.index := by
    rw [← Subgroup.index_comap_of_surjective S hπ₀, ← hPS]
    exact hS.2.2
  have hUi : ¬ 2 ∣ U.index := by
    have := hM.sylow.2.2
    change ¬ 2 ∣ U.relIndex ⊤ at this
    rwa [Subgroup.relIndex_top_right] at this
  obtain ⟨m, hm⟩ := exists_conj_sylow hSp hSi hM.sylow.2.1 hUi
  set π : ↥K →* M := (MulAut.conj m).toMonoidHom.comp π₀ with hπdef
  have hπx : ∀ x : ↥K, π x = m * π₀ x * m⁻¹ := fun x => rfl
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨x, hx⟩ := hπ₀ (m⁻¹ * y * m)
    exact ⟨x, by rw [hπx, hx]; group⟩
  have hπ1 : ∀ x : ↥K, π x = 1 ↔ π₀ x = 1 := fun x => by
    rw [hπx]
    exact conj_eq_one_iff m _
  have hkerπ : π.ker = π₀.ker := by
    ext x
    simp only [MonoidHom.mem_ker]
    exact hπ1 x
  have hπU : ∀ x : ↥K, π x ∈ U ↔ (x : G) ∈ P := by
    intro x
    rw [hm, hπx]
    have e : m⁻¹ * (m * π₀ x * m⁻¹) * m = π₀ x := by group
    rw [e]
    have h1 : π₀ x ∈ S ↔ x ∈ P' := by
      rw [hPS]
      rfl
    rw [h1, hP'def, Subgroup.mem_subgroupOf]
  refine ⟨π, hπ, fun x hx => hkc x ((hπ1 x).mp hx), hkerπ ▸ hk2, fun x hx => (hπ1 x).mpr (hcen x hx),
    ?_⟩
  ext x
  rw [mem_pre]
  constructor
  · intro hx
    exact ⟨hS.1 hx, (hπU ⟨x, hS.1 hx⟩).mpr hx⟩
  · rintro ⟨h, hU⟩
    exact (hπU ⟨x, h⟩).mp hU


theorem exists_induced_aut {G : Type} [Group G] {K : Subgroup G} {M : Type} [Group M]
    {π : ↥K →* M} (hπ : Function.Surjective π)
    (hcen : ∀ x : ↥K, (∀ y : ↥K, x * y = y * x) → π x = 1)
    (hker : ∀ x : ↥K, π x = 1 → ∀ y : ↥K, x * y = y * x)
    {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    ∃ α : MulAut M, ∀ (x : ↥K) (hx : g⁻¹ * (x : G) * g ∈ K), α (π x) = π ⟨g⁻¹ * x * g, hx⟩ := by
  have hgK' : ∀ x ∈ K, g⁻¹ * x * g ∈ K := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
    simpa using this
  have hgK'' : ∀ x ∈ K, g * x * g⁻¹ ∈ K := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  let β : ↥K ≃* ↥K :=
    { toFun := fun x => ⟨g⁻¹ * x * g, hgK' x x.2⟩
      invFun := fun x => ⟨g * x * g⁻¹, hgK'' x x.2⟩
      left_inv := fun x => by apply Subtype.ext; simp [mul_assoc]
      right_inv := fun x => by apply Subtype.ext; simp [mul_assoc]
      map_mul' := fun x y => by apply Subtype.ext; simp only [Subgroup.coe_mul]; group }
  have hcentral : ∀ (γ : ↥K ≃* ↥K) (x : ↥K), (∀ y, x * y = y * x) → ∀ y, γ x * y = y * γ x := by
    intro γ x hx y
    have := hx (γ.symm y)
    have h2 := congrArg γ this
    simpa using h2
  have hβker : π.ker.map β.toMonoidHom = π.ker := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact MonoidHom.mem_ker.mpr (hcen _ (hcentral β x (hker x (MonoidHom.mem_ker.mp hx))))
    · intro hy
      refine ⟨β.symm y, ?_, by simp⟩
      exact MonoidHom.mem_ker.mpr (hcen _ (hcentral β.symm y (hker y (MonoidHom.mem_ker.mp hy))))
  refine ⟨inducedAut π hπ β hβker, fun x hx => ?_⟩
  exact inducedAut_apply π hπ β hβker x

theorem centralizes_of_acts_trivially {G : Type} [Group G] {K : Subgroup G} {M : Type} [Group M]
    {π : ↥K →* M} (hq : CFSG.IsQuasisimple ↥K)
    (hker : ∀ x : ↥K, π x = 1 → ∀ y : ↥K, x * y = y * x)
    {g : G} (hgK : ∀ x ∈ K, g⁻¹ * x * g ∈ K)
    (h1 : ∀ (x : ↥K) (hx : g⁻¹ * (x : G) * g ∈ K), π ⟨g⁻¹ * x * g, hx⟩ = π x) :
    g ∈ Subgroup.centralizer (K : Set G) := by
  have hZcen : ∀ z ∈ pre π (⊥ : Subgroup M), ∀ x ∈ K, z * x = x * z := by
    intro z hz x hx
    obtain ⟨hzK, hz1⟩ := mem_pre.mp hz
    exact congrArg Subtype.val (hker ⟨z, hzK⟩ (Subgroup.mem_bot.mp hz1) ⟨x, hx⟩)
  have hZab : ∀ z ∈ pre π (⊥ : Subgroup M), ∀ z' ∈ pre π (⊥ : Subgroup M), z * z' = z' * z :=
    fun z hz z' hz' => hZcen z hz z' (pre_le_K _ hz')
  have hgZ : ∀ x ∈ K, x⁻¹ * g⁻¹ * x * g ∈ pre π (⊥ : Subgroup M) := by
    intro x hx
    have hx' := hgK x hx
    have hK : x⁻¹ * g⁻¹ * x * g ∈ K := by
      have := K.mul_mem (K.inv_mem hx) hx'
      simpa [mul_assoc] using this
    refine mem_pre.mpr ⟨hK, ?_⟩
    have e : (⟨x⁻¹ * g⁻¹ * x * g, hK⟩ : ↥K) = (⟨x, hx⟩ : ↥K)⁻¹ * ⟨g⁻¹ * x * g, hx'⟩ := by
      apply Subtype.ext
      simp [mul_assoc]
    rw [e, map_mul, map_inv, h1 ⟨x, hx⟩ hx', inv_mul_cancel]
    exact Subgroup.one_mem _
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  exact (centralizes_of_perfect K (pre π ⊥) hq.1.commutator_eq_top hZcen hZab g hgZ x hx).symm


theorem cover_aux {G : Type} [Group G] [Finite G] {K P : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥K) {M : Type} [Group M] [Finite M] {U R₁ R₂ : Subgroup M}
    {π : ↥K →* M} (hred : RedP257 K P π U) (hM : ModelData M U R₁ R₂)
    (hsup : Subgroup.normalizer (R₁ : Set M) ⊔ Subgroup.normalizer (R₂ : Set M) = ⊤)
    (hfix : ∀ w ∈ R₁ ⊓ R₂, (∀ b ∈ Subgroup.normalizer (U : Set M), b * w = w * b) → w = 1)
    (hZP : ∀ x : ↥K, π x ∈ R₁ ⊓ R₂ → (∀ y : ↥K, π y ∈ U → x * y = y * x) → π x = 1)
    {g : G} (hgK : g ∈ Subgroup.normalizer (K : Set G)) (hgP : ∀ y ∈ P, g * y = y * g) :
    g ∈ Subgroup.centralizer (K : Set G) := by
  obtain ⟨α, hα⟩ := exists_induced_aut hred.surj hred.center_le hred.ker_central hgK
  have hgK' : ∀ x ∈ K, g⁻¹ * x * g ∈ K := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hgK) x).mp hx
    simpa using this
  have hmemP : ∀ y : ↥K, π y ∈ U → (y : G) ∈ P := fun y hy => by
    rw [hred.hP]
    exact mem_pre_of_mem y hy
  have hαU : ∀ u ∈ U, α u = u := by
    intro u hu
    obtain ⟨y, rfl⟩ := hred.surj u
    have hc : g⁻¹ * (y : G) * g = y := by
      have := hgP y (hmemP y hu)
      calc g⁻¹ * y * g = g⁻¹ * (y * g) := by group
        _ = g⁻¹ * (g * y) := by rw [this]
        _ = y := by group
    have hy' : g⁻¹ * (y : G) * g ∈ K := by rw [hc]; exact y.2
    rw [hα y hy']
    congr 1
    exact Subtype.ext hc
  obtain ⟨w, hw, hαw⟩ := aut_eq_conj_of_fix hM hsup hfix α hαU
  have hwU : w ∈ U := hM.le₁ (Subgroup.mem_inf.mp hw).1
  obtain ⟨w', hw'⟩ := hred.surj w
  have hw'P : (w' : G) ∈ P := hmemP w' (by rw [hw']; exact hwU)
  have hhK : ∀ x ∈ K, g * w' * x = x * (g * w') := by
    have hgwK : ∀ x ∈ K, (g * (w' : G))⁻¹ * x * (g * w') ∈ K := fun x hx => by
      have h1 := K.mul_mem (K.mul_mem (K.inv_mem w'.2) (hgK' x hx)) w'.2
      simpa [mul_assoc] using h1
    have hc := centralizes_of_acts_trivially (π := π) hq hred.ker_central (g := g * (w' : G))
      (fun x hx => hgwK x hx) (fun x hx => by
        have hx' := hgK' x x.2
        have e : (⟨(g * (w' : G))⁻¹ * x * (g * w'), hx⟩ : ↥K) = w'⁻¹ * ⟨g⁻¹ * x * g, hx'⟩ * w' := by
          apply Subtype.ext
          simp [mul_assoc]
        rw [e, map_mul, map_mul, map_inv, hw', ← hα x hx', hαw]
        group)
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp hc x hx).symm
  have hcomm : ∀ y : ↥K, π y ∈ U → w' * y = y * w' := by
    intro y hy
    have hyP := hmemP y hy
    apply Subtype.ext
    show (w' : G) * y = y * w'
    apply mul_left_cancel (a := g)
    calc g * ((w' : G) * y) = g * w' * y := by group
      _ = y * (g * w') := hhK y y.2
      _ = (y * g) * w' := by group
      _ = (g * y) * w' := by rw [hgP y hyP]
      _ = g * (y * w') := by group
  have h1 : π w' = 1 := hZP w' (by rw [hw']; exact hw) hcomm
  have hw1 : w = 1 := by rw [← hw', h1]
  refine centralizes_of_acts_trivially (π := π) hq hred.ker_central hgK' (fun x hx => ?_)
  rw [← hα x hx, hαw, hw1]
  group

end CFSG.QuasithinUnique.Fin257
