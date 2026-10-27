module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualAbs

public section

namespace CFSG.QuasithinUnique.Borel252

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique.Fin257

structure OvergroupData (M : Type) [Group M] (U B P₀ P₁ : Subgroup M) : Prop where
  le_norm : B ≤ Subgroup.normalizer (U : Set M)
  cov₀ : B ⋖ P₀
  cov₁ : B ⋖ P₁
  cont : ∀ A : Subgroup M, U ≤ A → A ≠ ⊤ → A ≤ P₀ ∨ A ≤ P₁

theorem OvergroupData.eq_of_between {M : Type} [Group M] {U B P₀ P₁ : Subgroup M}
    (h : OvergroupData M U B P₀ P₁) {X : Subgroup M}
    (hX : Subgroup.normalizer (U : Set M) < X) (hXt : X < ⊤) : X = P₀ ∨ X = P₁ := by
  have hUX : U ≤ X := Subgroup.le_normalizer.trans hX.le
  have hBX : B < X := lt_of_le_of_lt h.le_norm hX
  rcases h.cont X hUX hXt.ne with hle | hle
  · left
    by_contra hne
    exact h.cov₀.2 hBX (lt_of_le_of_ne hle hne)
  · right
    by_contra hne
    exact h.cov₁.2 hBX (lt_of_le_of_ne hle hne)

theorem only_of_overgroupData {M : Type} [Group M] {U B P₀ P₁ : Subgroup M}
    (h : OvergroupData M U B P₀ P₁) {N₁ N₂ : Subgroup M}
    (h₁ : Subgroup.normalizer (U : Set M) < N₁) (h₁' : N₁ < ⊤)
    (h₂ : Subgroup.normalizer (U : Set M) < N₂) (h₂' : N₂ < ⊤) (hne : N₁ ≠ N₂)
    {X : Subgroup M} (hX : Subgroup.normalizer (U : Set M) < X) (hXt : X < ⊤) :
    X = N₁ ∨ X = N₂ := by
  rcases h.eq_of_between h₁ h₁' with e1 | e1 <;> rcases h.eq_of_between h₂ h₂' with e2 | e2 <;>
    rcases h.eq_of_between hX hXt with e3 | e3
  all_goals first
    | (exfalso; exact hne (e1.trans e2.symm))
    | (left; exact e3.trans e1.symm)
    | (right; exact e3.trans e2.symm)

theorem OvergroupData.of_cover {G₀ S : Type} [Group G₀] [Group S] {π : G₀ →* S}
    (hπ : Function.Surjective π) {V B : Subgroup G₀} {Q : Fin 2 → Subgroup G₀}
    (hker : π.ker ≤ B) (hcov : ∀ j, B ⋖ Q j)
    (hcont : ∀ A : Subgroup G₀, V ≤ A → A ≠ ⊤ → A ≤ Q 0 ∨ A ≤ Q 1)
    (hnorm : B.map π ≤ Subgroup.normalizer ((V.map π : Subgroup S) : Set S)) :
    OvergroupData S (V.map π) (B.map π) ((Q 0).map π) ((Q 1).map π) where
  le_norm := hnorm
  cov₀ := Setup.X7a.covBy_map_of_ker_le hπ hker (hcov 0)
  cov₁ := Setup.X7a.covBy_map_of_ker_le hπ hker (hcov 1)
  cont := by
    intro A hUA hAt
    have hV : V ≤ A.comap π := Subgroup.map_le_iff_le_comap.mp hUA
    have hAt' : A.comap π ≠ ⊤ := by
      intro h
      apply hAt
      rw [← Subgroup.map_comap_eq_self_of_surjective hπ A, h, Subgroup.map_top_of_surjective _ hπ]
    rcases hcont _ hV hAt' with h | h
    · left
      rw [← Subgroup.map_comap_eq_self_of_surjective hπ A]
      exact Subgroup.map_mono h
    · right
      rw [← Subgroup.map_comap_eq_self_of_surjective hπ A]
      exact Subgroup.map_mono h

theorem OvergroupData.map {M M' : Type} [Group M] [Group M'] (φ : M ≃* M')
    {U B P₀ P₁ : Subgroup M} (h : OvergroupData M U B P₀ P₁) :
    OvergroupData M' (U.map φ.toMonoidHom) (B.map φ.toMonoidHom) (P₀.map φ.toMonoidHom)
      (P₁.map φ.toMonoidHom) := by
  have hker : (φ.toMonoidHom).ker ≤ B := by
    intro x hx
    have : x = 1 := φ.injective (by simpa using hx)
    rw [this]
    exact B.one_mem
  have hsurj : Function.Surjective φ.toMonoidHom := φ.surjective
  refine ⟨?_, Setup.X7a.covBy_map_of_ker_le hsurj hker h.cov₀,
    Setup.X7a.covBy_map_of_ker_le hsurj hker h.cov₁, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    have hb := h.le_norm hb
    rw [Subgroup.mem_normalizer_iff] at hb ⊢
    intro y
    obtain ⟨x, rfl⟩ := φ.surjective y
    constructor
    · rintro ⟨u, hu, hux⟩
      have hux' : u = x := φ.injective hux
      subst hux'
      refine ⟨b * u * b⁻¹, (hb u).mp hu, ?_⟩
      simp
    · rintro ⟨u, hu, hux⟩
      refine ⟨x, ?_, rfl⟩
      have hux' : b * x * b⁻¹ = u := φ.injective (by simpa using hux.symm)
      show x ∈ U
      rw [hb x, hux']
      exact hu
  · intro A hUA hAt
    have hV : U ≤ A.comap φ.toMonoidHom := Subgroup.map_le_iff_le_comap.mp hUA
    have hAt' : A.comap φ.toMonoidHom ≠ ⊤ := by
      intro h
      apply hAt
      rw [← Subgroup.map_comap_eq_self_of_surjective hsurj A, h,
        Subgroup.map_top_of_surjective _ hsurj]
    rcases h.cont _ hV hAt' with h' | h'
    · left
      rw [← Subgroup.map_comap_eq_self_of_surjective hsurj A]
      exact Subgroup.map_mono h'
    · right
      rw [← Subgroup.map_comap_eq_self_of_surjective hsurj A]
      exact Subgroup.map_mono h'

structure BorelData (M : Type) [Group M] (U R₁ R₂ : Subgroup M) : Prop where
  center_trivial : ∀ m : M, (∀ y : M, m * y = y * m) → m = 1
  sylow : IsSylowTwoOf U ⊤
  le₁ : R₁ ≤ U
  le₂ : R₂ ≤ U
  sup : R₁ ⊔ R₂ = U
  cent₁ : ∀ g : M, (∀ r ∈ R₁, g * r = r * g) → g ∈ R₁
  cent₂ : ∀ g : M, (∀ r ∈ R₂, g * r = r * g) → g ∈ R₂
  lt₁ : Subgroup.normalizer (U : Set M) < Subgroup.normalizer (R₁ : Set M)
  lt₂ : Subgroup.normalizer (U : Set M) < Subgroup.normalizer (R₂ : Set M)
  lt_top₁ : Subgroup.normalizer (R₁ : Set M) < ⊤
  lt_top₂ : Subgroup.normalizer (R₂ : Set M) < ⊤
  core₁ : pCoreOf 2 (Subgroup.normalizer (R₁ : Set M)) = R₁
  core₂ : pCoreOf 2 (Subgroup.normalizer (R₂ : Set M)) = R₂
  only : ∀ X : Subgroup M, Subgroup.normalizer (U : Set M) < X → X < ⊤ →
    X = Subgroup.normalizer (R₁ : Set M) ∨ X = Subgroup.normalizer (R₂ : Set M)

section Data

variable {M : Type} [Group M] {U R₁ R₂ : Subgroup M}

theorem ne_normalizer_of_sup {R₁ R₂ : Subgroup M} (hsup : R₁ ⊔ R₂ = U)
    (hlt : Subgroup.normalizer (U : Set M) < Subgroup.normalizer (R₁ : Set M)) :
    Subgroup.normalizer (R₁ : Set M) ≠ Subgroup.normalizer (R₂ : Set M) := by
  intro heq
  have hle : Subgroup.normalizer (R₁ : Set M) ≤ Subgroup.normalizer (U : Set M) := by
    intro q hq
    have hq2 : q ∈ Subgroup.normalizer (R₂ : Set M) := heq ▸ hq
    have hqi : q⁻¹ ∈ Subgroup.normalizer (R₁ : Set M) := inv_mem hq
    have hq2i : q⁻¹ ∈ Subgroup.normalizer (R₂ : Set M) := inv_mem hq2
    have hfw : ∀ q : M, q ∈ Subgroup.normalizer (R₁ : Set M) →
        q ∈ Subgroup.normalizer (R₂ : Set M) → ∀ x ∈ U, q * x * q⁻¹ ∈ U := by
      intro q hq hq2 x hx
      rw [← hsup] at hx ⊢
      exact conj_mem_sup (fun y hy => (Subgroup.mem_normalizer_iff.mp hq y).mp hy)
        (fun y hy => (Subgroup.mem_normalizer_iff.mp hq2 y).mp hy) x hx
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hfw q hq hq2 x, fun hx => ?_⟩
    have := hfw q⁻¹ hqi hq2i _ hx
    simpa [mul_assoc] using this
  exact absurd hlt (not_lt_of_ge hle)

theorem BorelData.ne_norm (h : BorelData M U R₁ R₂) :
    Subgroup.normalizer (R₁ : Set M) ≠ Subgroup.normalizer (R₂ : Set M) :=
  ne_normalizer_of_sup h.sup h.lt₁

theorem BorelData.isPGroup₁ (h : BorelData M U R₁ R₂) : IsPGroup 2 R₁ :=
  h.sylow.2.1.to_le h.le₁

theorem BorelData.isPGroup₂ (h : BorelData M U R₁ R₂) : IsPGroup 2 R₂ :=
  h.sylow.2.1.to_le h.le₂

theorem pCoreOf_normalizer_sylow (hU : IsSylowTwoOf U ⊤) :
    pCoreOf 2 (Subgroup.normalizer (U : Set M)) = U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · exact EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le hU Subgroup.le_normalizer)
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hU.2.1

theorem pCoreOf_normalizer_eq (hU : IsSylowTwoOf U ⊤) (hR : R₁ ≤ U)
    (hUN : U ≤ Subgroup.normalizer (R₁ : Set M))
    (hcore : ∀ c ∈ U, (∀ g ∈ Subgroup.normalizer (R₁ : Set M), g * c * g⁻¹ ∈ U) → c ∈ R₁) :
    pCoreOf 2 (Subgroup.normalizer (R₁ : Set M)) = R₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := isSylowTwoOf_of_le hU hUN
  apply le_antisymm
  · intro c hc
    have hcU : c ∈ U := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS hc
    refine hcore c hcU fun g hg => ?_
    have hnorm := le_normalizer_pCoreOf 2 (Subgroup.normalizer (R₁ : Set M)) hg
    have := (Subgroup.mem_normalizer_iff.mp hnorm c).mp hc
    exact EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS this
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
      (hU.2.1.to_le hR)

theorem BorelData.charTwo_borel (h : BorelData M U R₁ R₂) :
    CharTwo (Subgroup.normalizer (U : Set M)) := by
  unfold CharTwo
  rw [pCoreOf_normalizer_sylow h.sylow]
  intro x hx
  obtain ⟨-, hxc⟩ := Subgroup.mem_inf.mp hx
  have hx1 : x ∈ R₁ := h.cent₁ x fun r hr =>
    (Subgroup.mem_centralizer_iff.mp hxc r (h.le₁ hr)).symm
  exact h.le₁ hx1

theorem BorelData.charTwo₁ (h : BorelData M U R₁ R₂) :
    CharTwo (Subgroup.normalizer (R₁ : Set M)) := by
  unfold CharTwo
  rw [h.core₁]
  intro x hx
  obtain ⟨-, hxc⟩ := Subgroup.mem_inf.mp hx
  exact h.cent₁ x fun r hr => (Subgroup.mem_centralizer_iff.mp hxc r hr).symm

theorem BorelData.charTwo₂ (h : BorelData M U R₁ R₂) :
    CharTwo (Subgroup.normalizer (R₂ : Set M)) := by
  unfold CharTwo
  rw [h.core₂]
  intro x hx
  obtain ⟨-, hxc⟩ := Subgroup.mem_inf.mp hx
  exact h.cent₂ x fun r hr => (Subgroup.mem_centralizer_iff.mp hxc r hr).symm

theorem BorelData.sup_norm (h : BorelData M U R₁ R₂) :
    Subgroup.normalizer (R₁ : Set M) ⊔ Subgroup.normalizer (R₂ : Set M) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUN₁ : U ≤ Subgroup.normalizer (R₁ : Set M) :=
    Subgroup.le_normalizer.trans h.lt₁.le
  have hUN₂ : U ≤ Subgroup.normalizer (R₂ : Set M) :=
    Subgroup.le_normalizer.trans h.lt₂.le
  by_contra hne
  have hlt : Subgroup.normalizer (R₁ : Set M) ⊔ Subgroup.normalizer (R₂ : Set M) < ⊤ :=
    lt_top_iff_ne_top.mpr hne
  have hBlt : Subgroup.normalizer (U : Set M) <
      Subgroup.normalizer (R₁ : Set M) ⊔ Subgroup.normalizer (R₂ : Set M) :=
    lt_of_lt_of_le h.lt₁ le_sup_left
  rcases h.only _ hBlt hlt with e | e
  ·
    have h21 : Subgroup.normalizer (R₂ : Set M) ≤ Subgroup.normalizer (R₁ : Set M) := by
      rw [← e]
      exact le_sup_right
    have hR : R₁ ≤ R₂ := by
      have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (h.le₁.trans hUN₂) h21 h.isPGroup₁
      rwa [h.core₂] at this
    have hUR : U = R₂ := by
      rw [← h.sup]
      exact sup_eq_right.mpr hR
    exact h.lt₂.ne (by rw [hUR])
  ·
    have h12 : Subgroup.normalizer (R₁ : Set M) ≤ Subgroup.normalizer (R₂ : Set M) := by
      rw [← e]
      exact le_sup_left
    have hR : R₂ ≤ R₁ := by
      have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (h.le₂.trans hUN₁) h12 h.isPGroup₂
      rwa [h.core₁] at this
    have hUR : U = R₁ := by
      rw [← h.sup]
      exact sup_eq_left.mpr hR
    exact h.lt₁.ne (by rw [hUR])

end Data

theorem reduceB {G : Type} [Group G] [Finite G] {K P : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥K) {M : Type} [Group M] [Finite M] [Nontrivial M] {U : Subgroup M}
    (hcen : ∀ m : M, (∀ y : M, m * y = y * m) → m = 1) (hU : IsSylowTwoOf U ⊤)
    (π₀ : ↥K →* M) (hπ₀ : Function.Surjective π₀) (hker : IsPGroup 2 π₀.ker)
    (hS : IsSylowTwoOf P K) : ∃ π : ↥K →* M, RedP257 K P π U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen' : ∀ x : ↥K, (∀ y, x * y = y * x) → π₀ x = 1 := fun x hx =>
    center_le_ker hcen π₀ hπ₀ x hx
  have hkc : ∀ x : ↥K, π₀ x = 1 → ∀ y, x * y = y * x :=
    ker_central_of_quasisimple hq π₀ hπ₀ hcen'
  set P' := P.subgroupOf K with hP'def
  have hkerP : ∀ x : ↥K, π₀ x = 1 → x ∈ P' := by
    intro x hx
    have hx' : x ∈ CFSG.Open.pCore 2 ↥K := le_pCore 2 (MonoidHom.normal_ker π₀) hker hx
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
    have := hU.2.2
    change ¬ 2 ∣ U.relIndex ⊤ at this
    rwa [Subgroup.relIndex_top_right] at this
  obtain ⟨m, hm⟩ := exists_conj_sylow hSp hSi hU.2.1 hUi
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
  refine ⟨π, hπ, fun x hx => hkc x ((hπ1 x).mp hx), hkerπ ▸ hker,
    fun x hx => (hπ1 x).mpr (hcen' x hx), ?_⟩
  ext x
  rw [mem_pre]
  constructor
  · intro hx
    exact ⟨hS.1 hx, (hπU ⟨x, hS.1 hx⟩).mpr hx⟩
  · rintro ⟨h, hU⟩
    exact (hπU ⟨x, h⟩).mp hU

theorem charTwo_pre {G : Type} [Group G] [Finite G] {K : Subgroup G} {M : Type} [Group M]
    [Finite M] {π : ↥K →* M} (hπ : Function.Surjective π) (hker : IsPGroup 2 π.ker)
    {Q : Subgroup M} (hQ : CharTwo Q) : CharTwo (pre π Q) := by
  unfold CharTwo at hQ ⊢
  rw [pCoreOf_pre hπ hker Q]
  intro x hx
  obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxK, hπxQ⟩ := mem_pre.mp hxQ
  have hcent : π ⟨x, hxK⟩ ∈ Subgroup.centralizer (pCoreOf 2 Q : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := hπ y
    have hk : (k : G) ∈ pre π (pCoreOf 2 Q) := mem_pre_of_mem k hy
    have h1 := Subgroup.mem_centralizer_iff.mp hxC k hk
    have h2 : k * (⟨x, hxK⟩ : ↥K) = ⟨x, hxK⟩ * k := Subtype.ext h1
    rw [← map_mul, ← map_mul, h2]
  have := hQ (Subgroup.mem_inf.mpr ⟨hπxQ, hcent⟩)
  exact mem_pre.mpr ⟨hxK, this⟩

theorem borelFacts_of_data {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥L) (hS : IsSylowTwoOf P L)
    {M : Type} [Group M] [Finite M] {U R₁ R₂ : Subgroup M} (hM : BorelData M U R₁ R₂)
    (π₀ : ↥L →* M) (hπ₀ : Function.Surjective π₀) (hker : IsPGroup 2 π₀.ker) :
    CharTwo (L ⊓ Subgroup.normalizer (P : Set G)) ∧
      ∃ P₁ P₂ : Subgroup G,
        L ⊓ Subgroup.normalizer (P : Set G) < P₁ ∧ P₁ < L ∧
        L ⊓ Subgroup.normalizer (P : Set G) < P₂ ∧ P₂ < L ∧ P₁ ≠ P₂ ∧ P₁ ⊔ P₂ = L ∧
        (∀ X : Subgroup G, L ⊓ Subgroup.normalizer (P : Set G) < X → X < L →
          X = P₁ ∨ X = P₂) ∧
        CharTwo P₁ ∧ CharTwo P₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial M := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    exact hM.lt_top₁.ne (Subgroup.ext fun x => by simp [Subsingleton.elim x 1])
  obtain ⟨π, hπ⟩ := reduceB hq hM.center_trivial hM.sylow π₀ hπ₀ hker hS
  have hsurj := hπ.surj
  have hB : L ⊓ Subgroup.normalizer (P : Set G) = pre π (Subgroup.normalizer (U : Set M)) := by
    rw [pre_normalizer hsurj, ← hπ.hP]
  have hLtop : pre π (⊤ : Subgroup M) = L := pre_top
  refine ⟨?_, pre π (Subgroup.normalizer (R₁ : Set M)), pre π (Subgroup.normalizer (R₂ : Set M)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hB]
    exact charTwo_pre hsurj hπ.ker_two hM.charTwo_borel
  · rw [hB]
    exact (pre_lt_iff hsurj).mpr hM.lt₁
  · have := (pre_lt_iff hsurj).mpr hM.lt_top₁
    rwa [hLtop] at this
  · rw [hB]
    exact (pre_lt_iff hsurj).mpr hM.lt₂
  · have := (pre_lt_iff hsurj).mpr hM.lt_top₂
    rwa [hLtop] at this
  · exact fun h => hM.ne_norm (pre_injective hsurj h)
  · rw [← pre_sup hsurj, hM.sup_norm, hLtop]
  · intro X hBX hXL
    have hXL' : X ≤ L := hXL.le
    have hkerX : ∀ z : ↥L, π z = 1 → (z : G) ∈ X := by
      intro z hz
      have hzP : (z : G) ∈ P := by
        rw [hπ.hP]
        exact mem_pre_of_mem z (by rw [hz]; exact U.one_mem)
      exact hBX.le (Subgroup.mem_inf.mpr ⟨z.2, Subgroup.le_normalizer hzP⟩)
    set X' : Subgroup M := (X.subgroupOf L).map π with hX'
    have hpreX : pre π X' = X := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxL, y, hy, hyx⟩ := mem_pre.mp hx
        have h1 : π (y⁻¹ * ⟨x, hxL⟩) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
        have h2 := hkerX _ h1
        have hy' : (y : G) ∈ X := hy
        have h3 : (y : G) * ((y⁻¹ * ⟨x, hxL⟩ : ↥L) : G) ∈ X := X.mul_mem hy' h2
        have h4 : (y : G) * ((y⁻¹ * ⟨x, hxL⟩ : ↥L) : G) = x := by
          simp [Subgroup.coe_mul]
        rwa [h4] at h3
      · intro hx
        exact mem_pre.mpr ⟨hXL' hx, ⟨⟨x, hXL' hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩⟩
    have h1 : Subgroup.normalizer (U : Set M) < X' := by
      rw [← pre_lt_iff hsurj, hpreX, ← hB]
      exact hBX
    have h2 : X' < ⊤ := by
      rw [← pre_lt_iff hsurj, hpreX, hLtop]
      exact hXL
    rcases hM.only X' h1 h2 with e | e
    · left
      rw [← hpreX, e]
    · right
      rw [← hpreX, e]
  · exact charTwo_pre hsurj hπ.ker_two hM.charTwo₁
  · exact charTwo_pre hsurj hπ.ker_two hM.charTwo₂

end CFSG.QuasithinUnique.Borel252
