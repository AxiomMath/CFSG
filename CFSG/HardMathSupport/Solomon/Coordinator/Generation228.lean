module

public import CFSG.Open.Defs
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.SignalizerFunctorTheorem.Coprime.CommutatorGeneration
public import CFSG.GroupTheory.LocalCores.MinimalNormal
import CFSG.Foundations.KCoreOpen
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open

@[expose] def I_7_13_1_pPrime : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → ¬ p ∣ Nat.card K →
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 1

namespace Generation228

@[expose] def hyperplaneJoin {G : Type*} [Group G] (p : ℕ) (B X D : Subgroup G) : Subgroup G :=
  ⨆ (A : Subgroup G) (_ : A ≤ B ∧ (A.subgroupOf B).index ≤ p),
    ⁅X ⊓ Subgroup.centralizer (A : Set G), D⁆

@[expose] def Claim (p n m : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B X D : Subgroup G), Nat.card B = n → Nat.card X = m →
    IsElemAbelian p B → B ≤ Subgroup.normalizer (X : Set G) → ¬ p ∣ Nat.card X →
    IsKGroup ↥X → D ≤ B → ⁅X, D⁆ ≤ hyperplaneJoin p B X D

section Tools

variable {G : Type*} [Group G]

open scoped commutatorElement

theorem tools_comm_of_mem {p : ℕ} {B : Subgroup G} (hB : IsElemAbelian p B) {a b : G}
    (ha : a ∈ B) (hb : b ∈ B) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hB ha hb

theorem tools_le_normalizer {B S : Subgroup G} (h : ∀ g ∈ B, ∀ y ∈ S, g * y * g⁻¹ ∈ S) :
    B ≤ Subgroup.normalizer (S : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h g hg y hy, fun hy => ?_⟩
  have := h g⁻¹ (B.inv_mem hg) _ hy
  simpa [mul_assoc] using this

theorem tools_mem_of_normalizer {S : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (S : Set G))
    {y : G} (hy : y ∈ S) : g * y * g⁻¹ ∈ S :=
  (Subgroup.mem_normalizer_iff.mp hg y).mp hy

theorem tools_conj_comm_mem {X D : Subgroup G} {g : G} (hgX : ∀ x ∈ X, g * x * g⁻¹ ∈ X)
    (hgD : ∀ d ∈ D, g * d * g⁻¹ ∈ D) : ∀ y ∈ ⁅X, D⁆, g * y * g⁻¹ ∈ ⁅X, D⁆ := by
  have h : ⁅X, D⁆ ≤ Subgroup.comap (MulAut.conj g).toMonoidHom ⁅X, D⁆ := by
    rw [Subgroup.commutator_le]
    intro x hx d hd
    rw [Subgroup.mem_comap]
    have : (MulAut.conj g).toMonoidHom ⁅x, d⁆ =
        ⁅(MulAut.conj g).toMonoidHom x, (MulAut.conj g).toMonoidHom d⁆ :=
      map_commutatorElement _ _ _
    rw [this]
    exact Subgroup.commutator_mem_commutator (hgX x hx) (hgD d hd)
  intro y hy
  exact h hy

theorem hyperplaneJoin_mono {p : ℕ} {B X X' D : Subgroup G} (h : X ≤ X') :
    hyperplaneJoin p B X D ≤ hyperplaneJoin p B X' D := by
  unfold hyperplaneJoin
  exact iSup_mono fun A => iSup_mono fun hA =>
    Subgroup.commutator_mono (inf_le_inf_right _ h) le_rfl

theorem hyperplaneJoin_le_comm {p : ℕ} {B X D : Subgroup G} :
    hyperplaneJoin p B X D ≤ ⁅X, D⁆ := by
  unfold hyperplaneJoin
  exact iSup₂_le fun A _ => Subgroup.commutator_mono inf_le_left le_rfl

theorem comm_le_hyperplaneJoin_of_card_le [Finite G] {p : ℕ} {B X D : Subgroup G}
    (h : Nat.card B ≤ p) : ⁅X, D⁆ ≤ hyperplaneJoin p B X D := by
  unfold hyperplaneJoin
  refine le_iSup₂_of_le (⊥ : Subgroup G) ⟨bot_le, ?_⟩ ?_
  · rw [Subgroup.bot_subgroupOf, Subgroup.index_bot]
    exact h
  · have : Subgroup.centralizer (((⊥ : Subgroup G) : Subgroup G) : Set G) = ⊤ := by
      rw [eq_top_iff]
      intro g _
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have : h = 1 := by simpa using hh
      simp [this]
    rw [this, inf_top_eq]

theorem comm_le_of_le_normalizer {X D : Subgroup G} (hDX : D ≤ Subgroup.normalizer (X : Set G)) :
    ⁅X, D⁆ ≤ X := by
  rw [Subgroup.commutator_le]
  intro x hx d hd
  have h1 : d * x⁻¹ * d⁻¹ ∈ X := tools_mem_of_normalizer (hDX hd) (X.inv_mem hx)
  have : ⁅x, d⁆ = x * (d * x⁻¹ * d⁻¹) := by
    simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact X.mul_mem hx h1

theorem normalizer_comm {p : ℕ} {B X D : Subgroup G} (hB : IsElemAbelian p B)
    (hBX : B ≤ Subgroup.normalizer (X : Set G)) (hDB : D ≤ B) :
    B ≤ Subgroup.normalizer ((⁅X, D⁆ : Subgroup G) : Set G) := by
  refine tools_le_normalizer fun β hβ => tools_conj_comm_mem (fun x hx => ?_) (fun d hd => ?_)
  · exact tools_mem_of_normalizer (hBX hβ) hx
  · have := tools_comm_of_mem hB hβ (hDB hd)
    have e : β * d * β⁻¹ = d := by rw [this]; simp
    rw [e]
    exact hd

theorem normalizer_hyperplaneJoin {p : ℕ} {B X D : Subgroup G} (hB : IsElemAbelian p B)
    (hBX : B ≤ Subgroup.normalizer (X : Set G)) (hDB : D ≤ B) :
    B ≤ Subgroup.normalizer (hyperplaneJoin p B X D : Set G) := by
  refine tools_le_normalizer fun β hβ => ?_
  have h : hyperplaneJoin p B X D ≤
      Subgroup.comap (MulAut.conj β).toMonoidHom (hyperplaneJoin p B X D) := by
    unfold hyperplaneJoin
    refine iSup₂_le fun A hA => ?_
    rw [Subgroup.commutator_le]
    intro x hx d hd
    rw [Subgroup.mem_comap]
    have e : (MulAut.conj β).toMonoidHom ⁅x, d⁆ =
        ⁅(MulAut.conj β).toMonoidHom x, (MulAut.conj β).toMonoidHom d⁆ :=
      map_commutatorElement _ _ _
    rw [e]
    have hd' : (MulAut.conj β).toMonoidHom d = d := by
      have := tools_comm_of_mem hB hβ (hDB hd)
      change β * d * β⁻¹ = d
      rw [this]; simp
    rw [hd']
    have hx' : (MulAut.conj β).toMonoidHom x ∈ X ⊓ Subgroup.centralizer (A : Set G) := by
      refine ⟨tools_mem_of_normalizer (hBX hβ) hx.1, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro a ha
      have hxa := (Subgroup.mem_centralizer_iff.mp hx.2) a ha
      have haβ := tools_comm_of_mem hB (hA.1 ha) hβ
      change a * (β * x * β⁻¹) = β * x * β⁻¹ * a
      have haβ' := tools_comm_of_mem hB (hA.1 ha) (B.inv_mem hβ)
      calc a * (β * x * β⁻¹) = (a * β) * x * β⁻¹ := by group
        _ = β * a * x * β⁻¹ := by rw [haβ]
        _ = β * (a * x) * β⁻¹ := by group
        _ = β * (x * a) * β⁻¹ := by rw [hxa]
        _ = β * x * (a * β⁻¹) := by group
        _ = β * x * (β⁻¹ * a) := by rw [haβ']
        _ = β * x * β⁻¹ * a := by group
    have hle : ⁅X ⊓ Subgroup.centralizer (A : Set G), D⁆ ≤ hyperplaneJoin p B X D := by
      unfold hyperplaneJoin
      exact le_iSup₂_of_le A hA le_rfl
    exact hle (Subgroup.commutator_mem_commutator hx' hd)
  intro y hy
  exact h hy

theorem hyperplaneJoin_le {p : ℕ} {B X D : Subgroup G} (hDX : D ≤ Subgroup.normalizer (X : Set G)) :
    hyperplaneJoin p B X D ≤ X := by
  unfold hyperplaneJoin
  exact iSup₂_le fun A _ =>
    (Subgroup.commutator_mono inf_le_left le_rfl).trans (comm_le_of_le_normalizer hDX)

@[expose] def tools_smul {A N : Subgroup G} {y : G}
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hy : ∀ a ∈ A, y⁻¹ * (a * y * a⁻¹) ∈ N)
    (a : A) (n : N) : N :=
  ⟨y⁻¹ * ((a : G) * (y * n) * (a : G)⁻¹), by
    have e : y⁻¹ * ((a : G) * (y * n) * (a : G)⁻¹) =
        (y⁻¹ * (a * y * (a : G)⁻¹)) * (a * n * (a : G)⁻¹) := by group
    rw [e]
    exact N.mul_mem (hy a a.2) (tools_mem_of_normalizer (hAN a.2) n.2)⟩

theorem tools_smul_coe {A N : Subgroup G} {y : G}
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hy : ∀ a ∈ A, y⁻¹ * (a * y * a⁻¹) ∈ N)
    (a : A) (n : N) :
    ((tools_smul hAN hy a n : N) : G) = y⁻¹ * ((a : G) * (y * n) * (a : G)⁻¹) := rfl

@[expose, instance_reducible] def tools_cosetAction {A N : Subgroup G} {y : G}
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hy : ∀ a ∈ A, y⁻¹ * (a * y * a⁻¹) ∈ N) :
    MulAction A N where
  smul := tools_smul hAN hy
  one_smul n := by
    apply Subtype.ext
    show ((tools_smul hAN hy 1 n : N) : G) = n
    rw [tools_smul_coe]
    simp
  mul_smul a b n := by
    apply Subtype.ext
    show ((tools_smul hAN hy (a * b) n : N) : G) =
      ((tools_smul hAN hy a (tools_smul hAN hy b n) : N) : G)
    rw [tools_smul_coe, tools_smul_coe, tools_smul_coe]
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group

theorem exists_fixed_mem_coset [Finite G] {p : ℕ} (hp : p.Prime) {A N : Subgroup G}
    (hA : IsPGroup p A) (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hN : ¬ p ∣ Nat.card N)
    {y : G} (hy : ∀ a ∈ A, y⁻¹ * (a * y * a⁻¹) ∈ N) :
    ∃ n ∈ N, y * n ∈ Subgroup.centralizer (A : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  let _ : MulAction A N := tools_cosetAction hAN hy
  obtain ⟨n, hn⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card N hN
  refine ⟨n, n.2, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
  have h := MulAction.mem_fixedPoints.mp hn ⟨a, ha⟩
  have h2 : y⁻¹ * (a * (y * n) * a⁻¹) = n :=
    congrArg Subtype.val (show tools_smul hAN hy ⟨a, ha⟩ n = n from h)
  have h3 : a * (y * n) * a⁻¹ = y * n := by
    calc a * (y * n) * a⁻¹ = y * (y⁻¹ * (a * (y * n) * a⁻¹)) := by group
      _ = y * n := by rw [h2]
  calc a * (y * n) = a * (y * n) * a⁻¹ * a := by group
    _ = y * n * a := by rw [h3]

theorem tools_conj_comm_X {X D : Subgroup G} {c : G} (hc : c ∈ X) :
    ∀ y ∈ ⁅X, D⁆, c * y * c⁻¹ ∈ ⁅X, D⁆ := by
  have h : ⁅X, D⁆ ≤ Subgroup.comap (MulAut.conj c).toMonoidHom ⁅X, D⁆ := by
    rw [Subgroup.commutator_le]
    intro x hx d hd
    rw [Subgroup.mem_comap]
    have e : (MulAut.conj c).toMonoidHom ⁅x, d⁆ = ⁅c * x, d⁆ * ⁅c, d⁆⁻¹ := by
      change c * ⁅x, d⁆ * c⁻¹ = _
      simp only [commutatorElement_def]
      group
    rw [e]
    exact ⁅X, D⁆.mul_mem (Subgroup.commutator_mem_commutator (X.mul_mem hc hx) hd)
      (⁅X, D⁆.inv_mem (Subgroup.commutator_mem_commutator hc hd))
  intro y hy
  exact h hy

theorem comm_comm_eq [Finite G] {p : ℕ} (hp : p.Prime) {X D : Subgroup G} (hD : IsPGroup p D)
    (hDX : D ≤ Subgroup.normalizer (X : Set G)) (hX : ¬ p ∣ Nat.card X) :
    ⁅⁅X, D⁆, D⁆ = ⁅X, D⁆ := by
  have hDY : D ≤ Subgroup.normalizer ((⁅X, D⁆ : Subgroup G) : Set G) :=
    tools_le_normalizer fun g hg => tools_conj_comm_mem
      (fun x hx => tools_mem_of_normalizer (hDX hg) hx)
      (fun d hd => D.mul_mem (D.mul_mem hg hd) (D.inv_mem hg))
  have hYX : ⁅X, D⁆ ≤ X := comm_le_of_le_normalizer hDX
  apply le_antisymm (comm_le_of_le_normalizer hDY)
  have hYp : ¬ p ∣ Nat.card (⁅X, D⁆ : Subgroup G) := fun h =>
    hX (h.trans (Subgroup.card_dvd_of_le hYX))
  rw [Subgroup.commutator_le]
  intro x hx d hd
  obtain ⟨n, hn, hc⟩ := exists_fixed_mem_coset hp hD hDY hYp (y := x) (fun a ha => by
    have : x⁻¹ * (a * x * a⁻¹) = ⁅x⁻¹, a⁆ := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact Subgroup.commutator_mem_commutator (X.inv_mem hx) ha)
  have hcX : x * n ∈ X := X.mul_mem hx (hYX hn)
  have hcd : (x * n) * d = d * (x * n) :=
    ((Subgroup.mem_centralizer_iff.mp hc) d hd).symm
  have hcn : (x * n) * n⁻¹ * (x * n)⁻¹ ∈ ⁅X, D⁆ :=
    tools_conj_comm_X hcX n⁻¹ (⁅X, D⁆.inv_mem hn)
  have key : ⁅x, d⁆ = ⁅(x * n) * n⁻¹ * (x * n)⁻¹, d⁆ := by
    have h1 : d * (x * n) = (x * n) * d := hcd.symm
    calc ⁅x, d⁆ = x * n⁻¹ * x⁻¹ * (x * n) * d * x⁻¹ * d⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = x * n⁻¹ * x⁻¹ * (d * (x * n)) * x⁻¹ * d⁻¹ := by rw [h1]; group
      _ = _ := by simp only [commutatorElement_def]; group
  rw [key]
  exact Subgroup.commutator_mem_commutator hcn hd

theorem tools_isKGroup_of_injective {H G' : Type*} [Group H] [Group G'] (hG : IsKGroup G')
    (f : H →* G') (hf : Function.Injective f) : IsKGroup H :=
  hG.of_injective f hf

theorem isKGroup_of_le {X Y : Subgroup G} (hXK : IsKGroup ↥X) (hYX : Y ≤ X) : IsKGroup ↥Y :=
  tools_isKGroup_of_injective hXK (Subgroup.inclusion hYX) (Subgroup.inclusion_injective hYX)

theorem exists_minimal_invariant_normal [Finite G] {B X : Subgroup G} (hX1 : X ≠ ⊥)
    (hBX : B ≤ Subgroup.normalizer (X : Set G)) :
    ∃ N : Subgroup G, N ≤ X ∧ X ≤ Subgroup.normalizer (N : Set G) ∧
      B ≤ Subgroup.normalizer (N : Set G) ∧ N ≠ ⊥ ∧
      ∀ M : Subgroup G, M ≤ N → X ≤ Subgroup.normalizer (M : Set G) →
        B ≤ Subgroup.normalizer (M : Set G) → M = ⊥ ∨ M = N := by
  let S : Set (Subgroup G) := {N | N ≤ X ∧ X ≤ Subgroup.normalizer (N : Set G) ∧
    B ≤ Subgroup.normalizer (N : Set G) ∧ N ≠ ⊥}
  have hXS : X ∈ S := ⟨le_rfl, Subgroup.le_normalizer, hBX, hX1⟩
  obtain ⟨N, hN, hmin⟩ := WellFounded.has_min wellFounded_lt S ⟨X, hXS⟩
  refine ⟨N, hN.1, hN.2.1, hN.2.2.1, hN.2.2.2, fun M hM hXM hBM => ?_⟩
  by_cases hM1 : M = ⊥
  · exact Or.inl hM1
  · refine Or.inr ?_
    by_contra hne
    exact hmin M ⟨hM.trans hN.1, hXM, hBM, hM1⟩ (lt_of_le_of_ne hM hne)

theorem comm_le_of_comm_le_sup {X D N Z : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hZX : Z ≤ X)
    (hDZ : D ≤ Subgroup.normalizer (Z : Set G)) (h1 : X ≤ Z ⊔ N) (h2 : ⁅N, D⁆ ≤ Z) :
    ⁅X, D⁆ ≤ Z := by
  let P : Subgroup G :=
    { carrier := {w | ∃ z ∈ Z, ∃ n ∈ N, w = z * n}
      mul_mem' := by
        rintro _ _ ⟨z, hz, n, hn, rfl⟩ ⟨z', hz', n', hn', rfl⟩
        refine ⟨z * z', Z.mul_mem hz hz', (z'⁻¹ * n * z'⁻¹⁻¹) * n', ?_, ?_⟩
        · refine N.mul_mem ?_ hn'
          have := tools_mem_of_normalizer (hXN (hZX (Z.inv_mem hz'))) hn
          exact this
        · group
      one_mem' := ⟨1, Z.one_mem, 1, N.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨z, hz, n, hn, rfl⟩
        refine ⟨z⁻¹, Z.inv_mem hz, z * n⁻¹ * z⁻¹, ?_, ?_⟩
        · exact tools_mem_of_normalizer (hXN (hZX hz)) (N.inv_mem hn)
        · group }
  have hP : Z ⊔ N ≤ P := sup_le (fun z hz => ⟨z, hz, 1, N.one_mem, by simp⟩)
    (fun n hn => ⟨1, Z.one_mem, n, hn, by simp⟩)
  rw [Subgroup.commutator_le]
  intro x hx d hd
  obtain ⟨z, hz, n, hn, rfl⟩ := hP (h1 hx)
  have e : ⁅z * n, d⁆ = z * ⁅n, d⁆ * z⁻¹ * (z * (d * z⁻¹ * d⁻¹)) := by
    simp only [commutatorElement_def]; group
  rw [e]
  have h3 : ⁅n, d⁆ ∈ Z := h2 (Subgroup.commutator_mem_commutator hn hd)
  have h4 : d * z⁻¹ * d⁻¹ ∈ Z := tools_mem_of_normalizer (hDZ hd) (Z.inv_mem hz)
  exact Z.mul_mem (Z.mul_mem (Z.mul_mem hz h3) (Z.inv_mem hz)) (Z.mul_mem hz h4)

theorem solv_case [Finite G] {p : ℕ} (hp : p.Prime) {B X D : Subgroup G}
    (hB : IsElemAbelian p B) (hB2 : p ^ 2 ≤ Nat.card B)
    (hBX : B ≤ Subgroup.normalizer (X : Set G)) (hX : ¬ p ∣ Nat.card X)
    (hXs : Group.IsSolvable ↥X) (hDB : D ≤ B) : ⁅X, D⁆ ≤ hyperplaneJoin p B X D := by
  have hcop : Nat.Coprime p (Nat.card X) := hp.coprime_iff_not_dvd.2 hX
  rw [Subgroup.commutator_le]
  intro x hx d hd
  have hmem : ⁅x, d⁆ ∈ ⁅X, Subgroup.zpowers d⁆ :=
    Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers d)
  rw [CFSG.SignalizerFunctorTheorem.Coprime.commutator_eq_iSup_hyperplanes hp hB hB2 hBX hcop hXs
    (hDB hd)] at hmem
  have hle : (⨆ B' ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes p B,
      ⁅X ⊓ Subgroup.centralizer (B' : Set G), Subgroup.zpowers d⁆) ≤
        hyperplaneJoin p B X D := by
    refine iSup₂_le fun B' hB' => ?_
    refine le_trans (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.2 hd)) ?_
    have hidx : (B'.subgroupOf B).index ≤ p := by
      have h1 := Subgroup.card_mul_index (B'.subgroupOf B)
      have h2 : Nat.card (B'.subgroupOf B) = Nat.card B' :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB'.1).toEquiv
      rw [h2] at h1
      have hpos : 0 < Nat.card B' := Nat.card_pos
      have h3 : Nat.card B = p * Nat.card B' := hB'.2
      have h4 : (B'.subgroupOf B).index = p := by
        apply Nat.eq_of_mul_eq_mul_left hpos
        rw [h1, h3, mul_comm]
      exact h4.le
    unfold hyperplaneJoin
    exact le_iSup₂_of_le B' ⟨hB'.1, hidx⟩ le_rfl
  exact hle hmem

end Tools

section Transfer

theorem transfer_isKGroup_of_surjective {H H' : Type*} [Group H] [Group H'] (hH : IsKGroup H)
    (f : H →* H') (hf : Function.Surjective f) : IsKGroup H' :=
  hH.of_surjective f hf

section TransferSetup

variable {G : Type*} [Group G] {Q : Type*} [Group Q] (N : Subgroup G)
  (φ : ↥(Subgroup.normalizer (N : Set G)) →* Q)

@[expose] def transfer_img (S : Subgroup G) : Subgroup Q :=
  (S.subgroupOf (Subgroup.normalizer (N : Set G))).map φ

variable {N φ}

theorem transfer_mem_img {S : Subgroup G} {y : Q} :
    y ∈ transfer_img N φ S ↔ ∃ x : ↥(Subgroup.normalizer (N : Set G)), (x : G) ∈ S ∧ φ x = y := by
  simp [transfer_img, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem transfer_img_mem_of_mem {S : Subgroup G} (x : ↥(Subgroup.normalizer (N : Set G)))
    (hx : (x : G) ∈ S) : φ x ∈ transfer_img N φ S :=
  transfer_mem_img.2 ⟨x, hx, rfl⟩

theorem transfer_img_mono {S T : Subgroup G} (h : S ≤ T) :
    transfer_img N φ S ≤ transfer_img N φ T := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := transfer_mem_img.1 hy
  exact transfer_img_mem_of_mem x (h hx)

theorem transfer_img_eq_range {S : Subgroup G} (hS : S ≤ Subgroup.normalizer (N : Set G)) :
    transfer_img N φ S = (φ.comp (Subgroup.inclusion hS)).range := by
  ext y
  rw [MonoidHom.mem_range, transfer_mem_img]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨⟨s, hS s.2⟩, s.2, rfl⟩

theorem transfer_card_img_dvd [Finite G] {S : Subgroup G}
    (hS : S ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card (transfer_img N φ S) ∣ Nat.card S := by
  rw [transfer_img_eq_range hS]
  exact Subgroup.card_range_dvd _

theorem transfer_card_img_eq [Finite G] {S : Subgroup G}
    (hS : S ≤ Subgroup.normalizer (N : Set G))
    (hker : ∀ x : ↥(Subgroup.normalizer (N : Set G)), φ x = 1 ↔ (x : G) ∈ N)
    (hS1 : ∀ s ∈ S, s ∈ N → s = 1) :
    Nat.card (transfer_img N φ S) = Nat.card S := by
  rw [transfer_img_eq_range hS]
  have h := Subgroup.card_ker_mul_card_range (φ.comp (Subgroup.inclusion hS))
  have hk : (φ.comp (Subgroup.inclusion hS)).ker = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    have h1 : (s : G) ∈ N := (hker _).1 hs
    have := hS1 _ s.2 h1
    exact Subtype.ext this
  rw [hk, Subgroup.card_bot, one_mul] at h
  exact h

theorem transfer_card_img_lt [Finite G] {S : Subgroup G}
    (hS : S ≤ Subgroup.normalizer (N : Set G))
    (hker : ∀ x : ↥(Subgroup.normalizer (N : Set G)), φ x = 1 ↔ (x : G) ∈ N)
    (s : G) (hsS : s ∈ S) (hsN : s ∈ N) (hs1 : s ≠ 1) :
    Nat.card (transfer_img N φ S) < Nat.card S := by
  rw [transfer_img_eq_range hS]
  have h := Subgroup.card_ker_mul_card_range (φ.comp (Subgroup.inclusion hS))
  have hk : (φ.comp (Subgroup.inclusion hS)).ker ≠ ⊥ := by
    intro hk
    have : (⟨s, hsS⟩ : ↥S) ∈ (φ.comp (Subgroup.inclusion hS)).ker := by
      rw [MonoidHom.mem_ker]
      exact (hker ⟨s, hS hsS⟩).2 hsN
    rw [hk, Subgroup.mem_bot] at this
    exact hs1 (congrArg Subtype.val this)
  have h1 := (Subgroup.one_lt_card_iff_ne_bot _).2 hk
  have h2 : 0 < Nat.card (φ.comp (Subgroup.inclusion hS)).range :=
    Nat.pos_of_ne_zero fun h0 => by
      rw [h0, mul_zero] at h
      exact (Nat.card_pos (α := ↥S)).ne' h.symm
  nlinarith

open scoped commutatorElement in
theorem transfer_key {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Finite G]
    {B X D N : Subgroup G}
    (hB : IsElemAbelian p B) (hX : ¬ p ∣ Nat.card X)
    (hNX : N ≤ X) (hXN : X ≤ Subgroup.normalizer (N : Set G))
    (hBN : B ≤ Subgroup.normalizer (N : Set G))
    {Q : Type} [Group Q] [Finite Q] {φ : ↥(Subgroup.normalizer (N : Set G)) →* Q}
    (hker : ∀ x : ↥(Subgroup.normalizer (N : Set G)), φ x = 1 ↔ (x : G) ∈ N) :
    hyperplaneJoin p (transfer_img N φ B) (transfer_img N φ X) (transfer_img N φ D) ≤
      transfer_img N φ (hyperplaneJoin p B X D) := by
  unfold hyperplaneJoin
  refine iSup_le fun A' => iSup_le fun hA' => ?_
  obtain ⟨hA'B, hidx⟩ := hA'
  let A : Subgroup G := ((A'.comap φ).map (Subgroup.normalizer (N : Set G)).subtype) ⊓ B
  have hAB : A ≤ B := inf_le_right
  have memA : ∀ x : ↥(Subgroup.normalizer (N : Set G)), (x : G) ∈ B →
      ((x : G) ∈ A ↔ φ x ∈ A') := by
    intro x hx
    simp only [A, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.subtype_apply]
    constructor
    · rintro ⟨⟨y, hy, hyx⟩, -⟩
      have : y = x := Subtype.ext hyx
      rwa [← this]
    · intro h
      exact ⟨⟨x, h, rfl⟩, hx⟩
  have hidxA : (A.subgroupOf B).index ≤ p := by
    let ψ : ↥B →* ↥(transfer_img N φ B) :=
      (φ.comp (Subgroup.inclusion hBN)).codRestrict _
        (fun b => transfer_img_mem_of_mem (N := N) (φ := φ) ⟨b, hBN b.2⟩ b.2)
    have hψ : Function.Surjective ψ := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := transfer_mem_img.1 hy
      exact ⟨⟨x, hx⟩, rfl⟩
    have heq : A.subgroupOf B = (A'.subgroupOf (transfer_img N φ B)).comap ψ := by
      ext b
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact memA ⟨b, hBN b.2⟩ b.2
    rw [heq, Subgroup.index_comap_of_surjective _ hψ]
    exact hidx
  have hAp : IsPGroup p A := fun a => ⟨1, Subtype.ext (by simpa using hB.2 _ (hAB a.2))⟩
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := fun a ha => hBN (hAB ha)
  have hNp : ¬ p ∣ Nat.card N := fun h => hX (h.trans (Subgroup.card_dvd_of_le hNX))
  have hZ : ⁅X ⊓ Subgroup.centralizer (A : Set G), D⁆ ≤ hyperplaneJoin p B X D := by
    unfold hyperplaneJoin
    exact le_iSup₂_of_le (f := fun (A : Subgroup G) (_ : A ≤ B ∧ (A.subgroupOf B).index ≤ p) =>
      ⁅X ⊓ Subgroup.centralizer (A : Set G), D⁆) A ⟨hAB, hidxA⟩ le_rfl
  rw [Subgroup.commutator_le]
  intro y hy y' hy'
  obtain ⟨hyX, hyC⟩ := Subgroup.mem_inf.1 hy
  obtain ⟨x, hxX, rfl⟩ := transfer_mem_img.1 hyX
  obtain ⟨d, hdD, rfl⟩ := transfer_mem_img.1 hy'
  have hcomm : ∀ a ∈ A, ∀ a' : ↥(Subgroup.normalizer (N : Set G)), (a' : G) = a →
      φ a' * φ x = φ x * φ a' := by
    intro a ha a' ha'
    have h1 : φ a' ∈ A' := (memA a' (ha' ▸ hAB ha)).1 (ha' ▸ ha)
    exact Subgroup.mem_centralizer_iff.1 hyC _ h1
  have hy2 : ∀ a ∈ A, (x : G)⁻¹ * (a * x * a⁻¹) ∈ N := by
    intro a ha
    have haN : a ∈ Subgroup.normalizer (N : Set G) := hAN ha
    have := (hker (x⁻¹ * (⟨a, haN⟩ * x * ⟨a, haN⟩⁻¹))).1 (by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm a ha ⟨a, haN⟩ rfl]
      simp)
    simpa using this
  obtain ⟨n, hnN, hnC⟩ := exists_fixed_mem_coset hp hAp hAN hNp hy2
  have hnn : n ∈ Subgroup.normalizer (N : Set G) := hXN (hNX hnN)
  have hφn : φ ⟨n, hnn⟩ = 1 := (hker _).2 hnN
  have hmem := Subgroup.commutator_mem_commutator
    (H₁ := X ⊓ Subgroup.centralizer (A : Set G)) (H₂ := D)
    (Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ hxX (hNX hnN), hnC⟩) hdD
  have := transfer_img_mem_of_mem (N := N) (φ := φ)
    (x * ⟨n, hnn⟩ * d * (x * ⟨n, hnn⟩)⁻¹ * d⁻¹) (S := hyperplaneJoin p B X D)
    (hZ (by simpa [commutatorElement_def] using hmem))
  have e : ⁅φ x, φ d⁆ = φ (x * ⟨n, hnn⟩ * d * (x * ⟨n, hnn⟩)⁻¹ * d⁻¹) := by
    rw [commutatorElement_def]
    simp only [map_mul, map_inv, hφn, mul_one]
  rw [e]
  exact this

open scoped commutatorElement in
theorem transfer_core {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Finite G]
    {B X D N : Subgroup G}
    (hB : IsElemAbelian p B) (hBX : B ≤ Subgroup.normalizer (X : Set G))
    (hX : ¬ p ∣ Nat.card X) (hXK : IsKGroup ↥X) (hDB : D ≤ B)
    (hNX : N ≤ X) (hXN : X ≤ Subgroup.normalizer (N : Set G))
    (hBN : B ≤ Subgroup.normalizer (N : Set G)) (hN1 : N ≠ ⊥)
    {Q : Type} [Group Q] [Finite Q] {φ : ↥(Subgroup.normalizer (N : Set G)) →* Q}
    (hker : ∀ x : ↥(Subgroup.normalizer (N : Set G)), φ x = 1 ↔ (x : G) ∈ N) :
    Nat.card (transfer_img N φ B) = Nat.card B ∧
      Nat.card (transfer_img N φ X) < Nat.card X ∧
      IsElemAbelian p (transfer_img N φ B) ∧
      transfer_img N φ B ≤ Subgroup.normalizer (transfer_img N φ X : Set Q) ∧
      ¬ p ∣ Nat.card (transfer_img N φ X) ∧ IsKGroup ↥(transfer_img N φ X) ∧
      transfer_img N φ D ≤ transfer_img N φ B ∧
      (⁅transfer_img N φ X, transfer_img N φ D⁆ ≤
          hyperplaneJoin p (transfer_img N φ B) (transfer_img N φ X) (transfer_img N φ D) →
        ⁅X, D⁆ ≤ hyperplaneJoin p B X D ⊔ N) := by
  have hXn := hXN
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, transfer_img_mono hDB, ?_⟩
  · refine transfer_card_img_eq hBN hker fun b hb hbN => ?_
    have hbX : b ∈ X := hNX hbN
    have h1 : orderOf (⟨b, hbX⟩ : ↥X) ∣ Nat.card X := orderOf_dvd_natCard _
    have h2 : orderOf (⟨b, hbX⟩ : ↥X) ∣ p :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hB.2 b hb))
    rcases (Nat.dvd_prime hp).1 h2 with h3 | h3
    · have := orderOf_eq_one_iff.1 h3
      exact congrArg Subtype.val this
    · rw [h3] at h1
      exact absurd h1 hX
  · obtain ⟨⟨n, hnN⟩, hn1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hN1
    exact transfer_card_img_lt hXn hker n (hNX hnN) hnN (fun h => hn1 (Subtype.ext h))
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx, hxa⟩ := transfer_mem_img.1 a.2
      obtain ⟨y, hy, hyb⟩ := transfer_mem_img.1 b.2
      apply Subtype.ext
      show (a : Q) * b = b * a
      rw [← hxa, ← hyb, ← map_mul, ← map_mul]
      congr 1
      have := hB.1.is_comm.comm (⟨x, hx⟩ : ↥B) ⟨y, hy⟩
      exact Subtype.ext (congrArg (fun z : ↥B => (z : G)) this)
    · intro a ha
      obtain ⟨x, hx, rfl⟩ := transfer_mem_img.1 ha
      rw [← map_pow]
      have : x ^ p = 1 := Subtype.ext (by simpa using hB.2 _ hx)
      rw [this, map_one]
  · rw [Subgroup.le_normalizer_iff]
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := transfer_mem_img.1 ha
    obtain ⟨y, hy, rfl⟩ := transfer_mem_img.1 hb
    rw [← map_inv, ← map_mul, ← map_mul]
    refine transfer_img_mem_of_mem (x * y * x⁻¹) ?_
    simpa using Subgroup.le_normalizer_iff.1 hBX _ hx _ hy
  · exact fun h => hX (h.trans (transfer_card_img_dvd hXn))
  · rw [transfer_img_eq_range hXn]
    exact transfer_isKGroup_of_surjective hXK _
      (MonoidHom.rangeRestrict_surjective (φ.comp (Subgroup.inclusion hXn)))
  · intro h
    have hkey := transfer_key (D := D) hp hB hX hNX hXN hBN hker
    rw [Subgroup.commutator_le]
    intro x hx d hd
    have hxN : x ∈ Subgroup.normalizer (N : Set G) := hXN hx
    have hdN : d ∈ Subgroup.normalizer (N : Set G) := hBN (hDB hd)
    have h1 : ⁅φ ⟨x, hxN⟩, φ ⟨d, hdN⟩⁆ ∈ transfer_img N φ (hyperplaneJoin p B X D) :=
      hkey (h (Subgroup.commutator_mem_commutator
        (transfer_img_mem_of_mem ⟨x, hxN⟩ hx) (transfer_img_mem_of_mem ⟨d, hdN⟩ hd)))
    obtain ⟨z, hz, hzφ⟩ := transfer_mem_img.1 h1
    have e : φ (⟨x, hxN⟩ * ⟨d, hdN⟩ * ⟨x, hxN⟩⁻¹ * ⟨d, hdN⟩⁻¹) = φ z := by
      rw [hzφ, commutatorElement_def]
      simp only [map_mul, map_inv]
    have h2 : (z : G)⁻¹ * (x * d * x⁻¹ * d⁻¹) ∈ N := by
      have := (hker (z⁻¹ * (⟨x, hxN⟩ * ⟨d, hdN⟩ * ⟨x, hxN⟩⁻¹ * ⟨d, hdN⟩⁻¹))).1 (by
        rw [map_mul, map_inv, e, inv_mul_cancel])
      simpa using this
    have h3 : x * d * x⁻¹ * d⁻¹ = (z : G) * ((z : G)⁻¹ * (x * d * x⁻¹ * d⁻¹)) := by group
    rw [commutatorElement_def, h3]
    exact Subgroup.mul_mem_sup hz h2

end TransferSetup

theorem quot_transfer {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Finite G]
    {B X D N : Subgroup G}
    (hB : IsElemAbelian p B) (hBX : B ≤ Subgroup.normalizer (X : Set G))
    (hX : ¬ p ∣ Nat.card X) (hXK : IsKGroup ↥X) (hDB : D ≤ B)
    (hNX : N ≤ X) (hXN : X ≤ Subgroup.normalizer (N : Set G))
    (hBN : B ≤ Subgroup.normalizer (N : Set G)) (hN1 : N ≠ ⊥) :
    ∃ (G' : Type) (_ : Group G') (_ : Finite G') (B' X' D' : Subgroup G'),
      Nat.card B' = Nat.card B ∧ Nat.card X' < Nat.card X ∧ IsElemAbelian p B' ∧
      B' ≤ Subgroup.normalizer (X' : Set G') ∧ ¬ p ∣ Nat.card X' ∧ IsKGroup ↥X' ∧ D' ≤ B' ∧
      (⁅X', D'⁆ ≤ hyperplaneJoin p B' X' D' → ⁅X, D⁆ ≤ hyperplaneJoin p B X D ⊔ N) := by
  let φ : ↥(Subgroup.normalizer (N : Set G)) →*
      ↥(Subgroup.normalizer (N : Set G)) ⧸ N.subgroupOf (Subgroup.normalizer (N : Set G)) :=
    QuotientGroup.mk' _
  have hker : ∀ x : ↥(Subgroup.normalizer (N : Set G)), φ x = 1 ↔ (x : G) ∈ N := fun x => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact ⟨_, inferInstance, inferInstance, transfer_img N φ B, transfer_img N φ X,
    transfer_img N φ D, transfer_core hp hB hBX hX hXK hDB hNX hXN hBN hN1 hker⟩

end Transfer

section Reduction

section ReduceContribution

open scoped commutatorElement

theorem reduce_comm_of_isElemAbelian {p : ℕ} {G : Type*} [Group G] {B : Subgroup G}
    (hB : IsElemAbelian p B) {x y : G} (hx : x ∈ B) (hy : y ∈ B) : x * y = y * x :=
  CFSG.Open.IsElemAbelian.comm hB hx hy

theorem reduce_isElemAbelian_mono {p : ℕ} {G : Type*} [Group G] {B B' : Subgroup G}
    (hB : IsElemAbelian p B) (h : B' ≤ B) : IsElemAbelian p B' := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hB.2 x (h hx)⟩
  exact Subtype.ext (reduce_comm_of_isElemAbelian hB (h a.2) (h b.2))

theorem reduce_mem_sup_of_commute {G : Type*} [Group G] {S T : Subgroup G}
    (h : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) {x : G} :
    x ∈ S ⊔ T ↔ ∃ s ∈ S, ∃ t ∈ T, x = s * t := by
  constructor
  · intro hx
    let U : Subgroup G :=
      { carrier := {x | ∃ s ∈ S, ∃ t ∈ T, x = s * t}
        mul_mem' := by
          rintro _ _ ⟨s₁, hs₁, t₁, ht₁, rfl⟩ ⟨s₂, hs₂, t₂, ht₂, rfl⟩
          refine ⟨s₁ * s₂, S.mul_mem hs₁ hs₂, t₁ * t₂, T.mul_mem ht₁ ht₂, ?_⟩
          have := h s₂ hs₂ t₁ ht₁
          calc s₁ * t₁ * (s₂ * t₂) = s₁ * (t₁ * s₂) * t₂ := by group
            _ = s₁ * (s₂ * t₁) * t₂ := by rw [this]
            _ = s₁ * s₂ * (t₁ * t₂) := by group
        one_mem' := ⟨1, S.one_mem, 1, T.one_mem, by simp⟩
        inv_mem' := by
          rintro _ ⟨s, hs, t, ht, rfl⟩
          refine ⟨s⁻¹, S.inv_mem hs, t⁻¹, T.inv_mem ht, ?_⟩
          have := h s⁻¹ (S.inv_mem hs) t⁻¹ (T.inv_mem ht)
          rw [mul_inv_rev, this] }
    have hle : S ⊔ T ≤ U := sup_le (fun s hs => ⟨s, hs, 1, T.one_mem, by simp⟩)
      (fun t ht => ⟨1, S.one_mem, t, ht, by simp⟩)
    exact hle hx
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right ht)

theorem reduce_card_sup {G : Type*} [Group G] [Finite G] {S T : Subgroup G}
    (h : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) (hST : S ⊓ T = ⊥) :
    Nat.card ↥(S ⊔ T) = Nat.card S * Nat.card T := by
  let f : S × T → ↥(S ⊔ T) := fun st =>
    ⟨st.1 * st.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left st.1.2) (Subgroup.mem_sup_right st.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨s₁, t₁⟩ ⟨s₂, t₂⟩ hst
      have h1 : (s₁ : G) * t₁ = s₂ * t₂ := congrArg Subtype.val hst
      have h2 : (s₂ : G)⁻¹ * s₁ = t₂ * (t₁ : G)⁻¹ := by
        calc (s₂ : G)⁻¹ * s₁ = (s₂ : G)⁻¹ * (s₁ * t₁) * (t₁ : G)⁻¹ := by group
          _ = (s₂ : G)⁻¹ * (s₂ * t₂) * (t₁ : G)⁻¹ := by rw [h1]
          _ = t₂ * (t₁ : G)⁻¹ := by group
      have hmem : (s₂ : G)⁻¹ * s₁ ∈ S ⊓ T :=
        ⟨S.mul_mem (S.inv_mem s₂.2) s₁.2, h2 ▸ T.mul_mem t₂.2 (T.inv_mem t₁.2)⟩
      rw [hST, Subgroup.mem_bot] at hmem
      have hs : s₁ = s₂ := Subtype.ext (by
        have := congrArg (fun x => (s₂ : G) * x) hmem
        simpa using this)
      subst hs
      have : (t₁ : G) = t₂ := by simpa using h1
      exact Prod.ext rfl (Subtype.ext this)
    · rintro ⟨x, hx⟩
      obtain ⟨s, hs, t, ht, rfl⟩ := (reduce_mem_sup_of_commute h).1 hx
      exact ⟨(⟨s, hs⟩, ⟨t, ht⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem reduce_complement {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    {B C : Subgroup G} (hB : IsElemAbelian p B) :
    ∃ B' : Subgroup G, B' ≤ B ∧ C ⊓ B' = ⊥ ∧ ∀ b ∈ B, ∃ c ∈ C, ∃ b' ∈ B', b = c * b' := by
  let S : Set (Subgroup G) := {B' | B' ≤ B ∧ C ⊓ B' = ⊥}
  have hbot : (⊥ : Subgroup G) ∈ S := ⟨bot_le, by simp⟩
  obtain ⟨B', -, hmax⟩ := Set.Finite.exists_le_maximal (Set.toFinite S) hbot
  obtain ⟨⟨hB'B, hCB'⟩, hmax2⟩ := hmax
  refine ⟨B', hB'B, hCB', ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨b, hb, hbne⟩ := hcon
  have hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    reduce_comm_of_isElemAbelian hB hx hy
  have hcommB' : ∀ s ∈ B', ∀ t ∈ Subgroup.zpowers b, s * t = t * s := by
    intro s hs t ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
    exact hcomm s (hB'B hs) _ (Subgroup.zpow_mem _ hb k)
  have hbB'' : B' ⊔ Subgroup.zpowers b ≤ B :=
    sup_le hB'B ((Subgroup.zpowers_le).2 hb)
  have hbpow : b ^ p = 1 := hB.2 b hb
  have hS : B' ⊔ Subgroup.zpowers b ∈ S := by
    refine ⟨hbB'', ?_⟩
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxC, hxB''⟩ := hx
    obtain ⟨b', hb', t, ht, rfl⟩ := (reduce_mem_sup_of_commute hcommB').1 hxB''
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
    by_cases hk : (p : ℤ) ∣ k
    · obtain ⟨m, rfl⟩ := hk
      have h1 : b ^ ((p : ℤ) * m) = 1 := by rw [zpow_mul]; simp [hbpow]
      rw [h1, mul_one] at hxC ⊢
      have : b' ∈ C ⊓ B' := ⟨hxC, hb'⟩
      rw [hCB', Subgroup.mem_bot] at this
      rw [this]; exact Subgroup.one_mem _
    · exfalso
      have hcop : IsCoprime (k) (p : ℤ) := by
        have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
        exact (Prime.coprime_iff_not_dvd hpp |>.2 hk).symm
      obtain ⟨u, v, huv⟩ := hcop
      have hx' : (b' * b ^ k) ^ u ∈ C := Subgroup.zpow_mem _ hxC u
      refine hbne _ hx' ((b' ^ u)⁻¹) (B'.inv_mem (Subgroup.zpow_mem _ hb' u)) ?_
      have hbk : b = b ^ (u * k) := by
        have : b ^ (u * k) = b ^ (1 - v * p) := by rw [show u * k = 1 - v * p by linarith]
        rw [this, zpow_sub, zpow_one, mul_comm v (p : ℤ), zpow_mul, zpow_natCast, hbpow, one_zpow]
        simp
      have hcm : Commute b' (b ^ k) := hcommB' b' hb' _ (Subgroup.zpow_mem_zpowers b k)
      calc b = b ^ (u * k) := hbk
        _ = (b' * b ^ k) ^ u * (b' ^ u)⁻¹ := by
          rw [hcm.mul_zpow, ← zpow_mul, mul_comm u k]
          have h2 : Commute (b' ^ u) (b ^ (k * u)) := by rw [zpow_mul]; exact hcm.zpow_zpow u u
          rw [h2.eq]
          simp
  have := hmax2 hS (le_sup_left)
  exact hbne 1 C.one_mem b (this (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))) (by simp)
theorem reduce_comm_le {G : Type*} [Group G] {Y₀ D₁ D₂ C : Subgroup G}
    (hnorm : ∀ y ∈ Y₀, ∀ d ∈ D₂, d * y * d⁻¹ ∈ Y₀)
    (hC : ∀ c ∈ C, ∀ y ∈ Y₀, y * c = c * y)
    (hdec : ∀ d ∈ D₁, ∃ c ∈ C, ∃ d₂ ∈ D₂, d = c * d₂) : ⁅Y₀, D₁⁆ ≤ ⁅Y₀, D₂⁆ := by
  rw [Subgroup.commutator_le]
  intro y hy d hd
  obtain ⟨c, hc, d₂, hd₂, rfl⟩ := hdec d hd
  have hz : ⁅y, d₂⁆ ∈ Y₀ := by
    have : ⁅y, d₂⁆ = y * (d₂ * y⁻¹ * d₂⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact Y₀.mul_mem hy (hnorm y⁻¹ (Y₀.inv_mem hy) d₂ hd₂)
  have h1 : ⁅y, c * d₂⁆ = ⁅y, d₂⁆ := by
    have hyc := hC c hc y hy
    have hzc := hC c hc _ hz
    simp only [commutatorElement_def] at hzc ⊢
    calc y * (c * d₂) * y⁻¹ * (c * d₂)⁻¹ = (y * c) * d₂ * y⁻¹ * d₂⁻¹ * c⁻¹ := by group
      _ = c * (y * d₂ * y⁻¹ * d₂⁻¹) * c⁻¹ := by rw [hyc]; group
      _ = (y * d₂ * y⁻¹ * d₂⁻¹) * c * c⁻¹ := by rw [← hzc]
      _ = y * d₂ * y⁻¹ * d₂⁻¹ := by group
  rw [h1]
  exact Subgroup.commutator_mem_commutator hy hd₂

theorem reduce_conj_cent {G : Type*} [Group G] {p : ℕ} {B A : Subgroup G} (hB : IsElemAbelian p B)
    (hAB : A ≤ B) {d y : G} (hd : d ∈ B) (hy : y ∈ Subgroup.centralizer (A : Set G)) :
    d * y * d⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro a ha
  have hcad : Commute a d := reduce_comm_of_isElemAbelian hB (hAB ha) hd
  have hay : a * y = y * a := hy a ha
  calc a * (d * y * d⁻¹) = (a * d) * y * d⁻¹ := by group
    _ = d * (a * y) * d⁻¹ := by rw [hcad.eq]; group
    _ = d * y * (a * d⁻¹) := by rw [hay]; group
    _ = d * y * (d⁻¹ * a) := by rw [hcad.inv_right.eq]
    _ = d * y * d⁻¹ * a := by group

theorem reduce_B {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Finite G] {B Y D C : Subgroup G}
    (hB : IsElemAbelian p B) (hBY : B ≤ Subgroup.normalizer (Y : Set G)) (hDB : D ≤ B)
    (hCB : C ≤ B) (hCY : C ≤ Subgroup.centralizer (Y : Set G)) (hC1 : C ≠ ⊥)
    (hY : ¬ p ∣ Nat.card Y) (hYK : IsKGroup ↥Y)
    (ih : ∀ n' < Nat.card B, ∀ m', Claim p n' m') :
    ⁅Y, D⁆ ≤ hyperplaneJoin p B Y D := by
  obtain ⟨B', hB'B, hCB', hdec⟩ := reduce_complement hp hB (C := C)
  have hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    reduce_comm_of_isElemAbelian hB hx hy
  have hBeq : C ⊔ B' = B := by
    apply le_antisymm (sup_le hCB hB'B)
    intro b hb
    obtain ⟨c, hc, b', hb', rfl⟩ := hdec b hb
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hb')
  have hCB'comm : ∀ c ∈ C, ∀ b' ∈ B', c * b' = b' * c := fun c hc b' hb' =>
    hcomm c (hCB hc) b' (hB'B hb')
  have hBcard : Nat.card B = Nat.card C * Nat.card B' := by
    rw [← hBeq]; exact reduce_card_sup hCB'comm hCB'
  have hClt : Nat.card B' < Nat.card B := by
    have hCpos : 1 < Nat.card C := by
      rw [Nat.one_lt_iff_ne_zero_and_ne_one]
      refine ⟨Nat.card_pos.ne', ?_⟩
      intro h1
      exact hC1 ((Subgroup.card_eq_one).1 h1)
    rw [hBcard]
    have := Nat.card_pos (α := B')
    nlinarith
  set D' : Subgroup G := (D ⊔ C) ⊓ B' with hD'
  have hD'B' : D' ≤ B' := inf_le_right
  have hB'N : B' ≤ Subgroup.normalizer (Y : Set G) := hB'B.trans hBY
  have hih := ih (Nat.card B') hClt (Nat.card Y) G B' Y D' rfl rfl
    (reduce_isElemAbelian_mono hB hB'B) hB'N hY hYK hD'B'
  have hnormY : ∀ y ∈ Y, ∀ d ∈ B, d * y * d⁻¹ ∈ Y := fun y hy d hd =>
    (Subgroup.mem_normalizer_iff.1 (hBY hd) y).1 hy
  have ha : ⁅Y, D⁆ ≤ ⁅Y, D'⁆ := by
    refine reduce_comm_le (C := C) (fun y hy d hd => hnormY y hy d (hB'B (hD'B' hd)))
      (fun c hc y hy => ?_) ?_
    · exact ((Subgroup.mem_centralizer_iff.1 (hCY hc)) y hy)
    · intro d hd
      obtain ⟨c, hc, b', hb', rfl⟩ := hdec d (hDB hd)
      refine ⟨c, hc, b', ?_, rfl⟩
      refine ⟨?_, hb'⟩
      have : b' = c⁻¹ * (c * b') := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (C.inv_mem hc)) (Subgroup.mem_sup_left hd)
  have hb : hyperplaneJoin p B' Y D' ≤ hyperplaneJoin p B Y D := by
    refine iSup₂_le fun A' hA' => ?_
    obtain ⟨hA'B', hidx⟩ := hA'
    set A : Subgroup G := C ⊔ A' with hA
    have hAB : A ≤ B := sup_le hCB (hA'B'.trans hB'B)
    have hCA' : C ⊓ A' = ⊥ := le_bot_iff.1 (hCB' ▸ inf_le_inf_left C hA'B')
    have hcommA' : ∀ c ∈ C, ∀ a ∈ A', c * a = a * c := fun c hc a ha =>
      hcomm c (hCB hc) a (hB'B (hA'B' ha))
    have hAcard : Nat.card A = Nat.card C * Nat.card A' := reduce_card_sup hcommA' hCA'
    have hia : (A.subgroupOf B).index = (A'.subgroupOf B').index := by
      have h1 := Subgroup.card_mul_index (A.subgroupOf B)
      have h2 := Subgroup.card_mul_index (A'.subgroupOf B')
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv, hAcard] at h1
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'B').toEquiv] at h2
      have hpos : 0 < Nat.card C * Nat.card A' :=
        Nat.mul_pos Nat.card_pos Nat.card_pos
      refine Nat.eq_of_mul_eq_mul_left hpos ?_
      rw [h1, hBcard, ← h2, mul_assoc]
    have hAle : Y ⊓ Subgroup.centralizer (A' : Set G) ≤ Y ⊓ Subgroup.centralizer (A : Set G) := by
      intro y hy
      obtain ⟨hyY, hyA'⟩ := Subgroup.mem_inf.1 hy
      refine Subgroup.mem_inf.2 ⟨hyY, ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hyA' ⊢
      intro a ha
      obtain ⟨c, hc, a', ha', rfl⟩ := (reduce_mem_sup_of_commute hcommA').1 ha
      have h1 : y * c = c * y := Subgroup.mem_centralizer_iff.1 (hCY hc) y hyY
      have h2 : a' * y = y * a' := hyA' a' ha'
      calc c * a' * y = c * (a' * y) := by group
        _ = c * (y * a') := by rw [h2]
        _ = (c * y) * a' := by group
        _ = (y * c) * a' := by rw [h1]
        _ = y * (c * a') := by group
    have hsub : ⁅Y ⊓ Subgroup.centralizer (A' : Set G), D'⁆ ≤
        ⁅Y ⊓ Subgroup.centralizer (A : Set G), D⁆ := by
      refine (Subgroup.commutator_mono hAle le_rfl).trans ?_
      refine reduce_comm_le (C := C) ?_ ?_ ?_
      · intro y hy d hd
        obtain ⟨hyY, hyA⟩ := Subgroup.mem_inf.1 hy
        exact Subgroup.mem_inf.2 ⟨hnormY y hyY d (hDB hd), reduce_conj_cent hB hAB (hDB hd) hyA⟩
      · intro c hc y hy
        exact Subgroup.mem_centralizer_iff.1 (hCY hc) y (Subgroup.mem_inf.1 hy).1
      · intro d hd
        obtain ⟨hdDC, -⟩ := Subgroup.mem_inf.1 hd
        obtain ⟨d₀, hd₀, c, hc, rfl⟩ := (reduce_mem_sup_of_commute
          (fun d hd c hc => hcomm d (hDB hd) c (hCB hc))).1 hdDC
        refine ⟨c, hc, d₀, hd₀, ?_⟩
        exact hcomm _ (hDB hd₀) _ (hCB hc)
    exact hsub.trans (le_iSup₂_of_le A ⟨hAB, hia ▸ hidx⟩ le_rfl)
  exact ha.trans (hih.trans hb)
end ReduceContribution

end Reduction

section NonabelianCase

structure FactorData (p : ℕ) (G : Type) [Group G] (B X : Subgroup G) where
  r : ℕ
  r_pos : 0 < r
  K : Fin r → Subgroup G
  π : Fin r → G → G
  σ : G → Equiv.Perm (Fin r)
  K_le : ∀ i, K i ≤ X
  K_simple : ∀ i, IsSimpleGroup ↥(K i)
  K_nonab : ∀ i, ∃ a b : K i, a * b ≠ b * a
  K_norm : ∀ i, ∀ x ∈ X, ∀ k ∈ K i, x * k * x⁻¹ ∈ K i
  K_comm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x
  π_mem : ∀ i, ∀ g ∈ X, π i g ∈ K i
  π_mul : ∀ i, ∀ g ∈ X, ∀ h ∈ X, π i (g * h) = π i g * π i h
  π_self : ∀ i, ∀ k ∈ K i, π i k = k
  π_ne : ∀ i j, i ≠ j → ∀ k ∈ K j, π i k = 1
  π_ext : ∀ g ∈ X, ∀ h ∈ X, (∀ i, π i g = π i h) → g = h
  exists_of_coord : ∀ f : Fin r → G, (∀ i, f i ∈ K i) → ∃ g ∈ X, ∀ i, π i g = f i
  gen : ∀ Y : Subgroup G, (∀ i, K i ≤ Y) → X ≤ Y
  B_norm : ∀ β ∈ B, ∀ g ∈ X, β * g * β⁻¹ ∈ X
  σ_mul : ∀ β ∈ B, ∀ γ ∈ B, σ (β * γ) = σ β * σ γ
  σ_conj : ∀ β ∈ B, ∀ i, ∀ k ∈ K i, β * k * β⁻¹ ∈ K (σ β i)
  π_conj : ∀ β ∈ B, ∀ g ∈ X, ∀ i, π (σ β i) (β * g * β⁻¹) = β * π i g * β⁻¹
  trans : ∀ i j, ∃ β ∈ B, σ β i = j
  faithful : ∀ β ∈ B, (∀ i, ∀ k ∈ K i, β * k * β⁻¹ = k) → β = 1
  stab_card : ∀ i, ∀ S : Subgroup G, S ≤ B → (∀ β ∈ S, σ β i = i) → Nat.card S ≤ p

end NonabelianCase

section NonabelianAPI

namespace FactorData

variable {p : ℕ} {G : Type} [Group G] {B X : Subgroup G} (d : FactorData p G B X)

private theorem api_comm (hB : IsElemAbelian p B) {b e : G} (hb : b ∈ B) (he : e ∈ B) :
    b * e = e * b := CFSG.Open.IsElemAbelian.comm hB hb he

theorem σ_one : d.σ 1 = 1 := by
  have h := d.σ_mul 1 B.one_mem 1 B.one_mem
  simp only [mul_one] at h
  have h2 : d.σ 1 * d.σ 1 = d.σ 1 * 1 := by rw [mul_one, ← h]
  exact mul_left_cancel h2

theorem σ_pow {b : G} (hb : b ∈ B) (m : ℕ) : d.σ (b ^ m) = d.σ b ^ m := by
  induction m with
  | zero => simp [d.σ_one]
  | succ m ih =>
    rw [pow_succ, d.σ_mul _ (B.pow_mem hb m) _ hb, ih, pow_succ]

theorem σ_comm (hB : IsElemAbelian p B) {b e : G} (hb : b ∈ B) (he : e ∈ B) :
    d.σ b * d.σ e = d.σ e * d.σ b := by
  rw [← d.σ_mul b hb e he, ← d.σ_mul e he b hb, api_comm hB hb he]

theorem stab_all (hB : IsElemAbelian p B) {b : G} (hb : b ∈ B) {i j : Fin d.r}
    (hi : d.σ b i = i) : d.σ b j = j := by
  obtain ⟨γ, hγ, hγi⟩ := d.trans i j
  calc d.σ b j = d.σ b (d.σ γ i) := by rw [hγi]
    _ = (d.σ b * d.σ γ) i := rfl
    _ = (d.σ γ * d.σ b) i := by rw [d.σ_comm hB hb hγ]
    _ = d.σ γ (d.σ b i) := rfl
    _ = j := by rw [hi, hγi]

theorem orbit_free (hp : p.Prime) (hB : IsElemAbelian p B) {b : G} (hb : b ∈ B)
    {i : Fin d.r} (hbi : d.σ b i ≠ i) {m : ℕ} (hm0 : 0 < m) (hmp : m < p) :
    (d.σ b ^ m) i ≠ i := by
  intro h
  have h1 : d.σ (b ^ m) i = i := by rw [d.σ_pow hb]; exact h
  have h2 : d.σ b ^ m = 1 := by
    refine Equiv.ext fun j => ?_
    rw [← d.σ_pow hb m]
    exact d.stab_all hB (B.pow_mem hb m) h1
  have h3 : d.σ b ^ p = 1 := by
    rw [← d.σ_pow hb p, hB.2 b hb, d.σ_one]
  have h4 : orderOf (d.σ b) ∣ p := orderOf_dvd_of_pow_eq_one h3
  have h5 : orderOf (d.σ b) ∣ m := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime hp).1 h4 with h6 | h6
  · rw [orderOf_eq_one_iff] at h6
    exact hbi (by rw [h6]; rfl)
  · have := Nat.le_of_dvd hm0 h5
    omega

theorem coord_pow {b : G} (hb : b ∈ B) {c : G} (hc : c ∈ X) (hbc : b * c * b⁻¹ = c)
    (j : Fin d.r) (m : ℕ) :
    d.π ((d.σ b ^ m) j) c = b ^ m * d.π j c * (b ^ m)⁻¹ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : (d.σ b ^ (m + 1)) j = d.σ b ((d.σ b ^ m) j) := by
      rw [pow_succ']; rfl
    have h2 := d.π_conj b hb c hc ((d.σ b ^ m) j)
    rw [hbc] at h2
    rw [h1, h2, ih, pow_succ']
    group

theorem K_center (i : Fin d.r) {z : G} (hz : z ∈ d.K i) (h : ∀ k ∈ d.K i, z * k = k * z) :
    z = 1 := by
  have := d.K_simple i
  have hmem : (⟨z, hz⟩ : ↥(d.K i)) ∈ Subgroup.center ↥(d.K i) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (h g.1 g.2).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(d.K i)) with h0 | h0
  · rw [h0, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    obtain ⟨a, b, hab⟩ := d.K_nonab i
    have : a ∈ Subgroup.center ↥(d.K i) := by rw [h0]; trivial
    rw [Subgroup.mem_center_iff] at this
    exact hab (this b).symm

theorem K_perfect (i : Fin d.r) : ⁅d.K i, d.K i⁆ = d.K i := by
  have := d.K_simple i
  have hmap : Subgroup.map (d.K i).subtype ⁅(⊤ : Subgroup ↥(d.K i)), (⊤ : Subgroup ↥(d.K i))⁆ = ⁅d.K i, d.K i⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have htop : ⁅(⊤ : Subgroup ↥(d.K i)), (⊤ : Subgroup ↥(d.K i))⁆ = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (⁅(⊤ : Subgroup ↥(d.K i)), (⊤ : Subgroup ↥(d.K i))⁆) with h0 | h0
    · exfalso
      obtain ⟨a, b, hab⟩ := d.K_nonab i
      have : a * b * a⁻¹ * b⁻¹ ∈ ⁅(⊤ : Subgroup ↥(d.K i)), (⊤ : Subgroup ↥(d.K i))⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h0, Subgroup.mem_bot] at this
      apply hab
      calc a * b = a * b * a⁻¹ * b⁻¹ * b * a := by group
        _ = b * a := by rw [this]; group
    · exact h0
  rw [← hmap, htop, Subgroup.map_top, Subgroup.range_subtype]

theorem moves_all (hB : IsElemAbelian p B) {u : G} (hu : u ∈ B) (hu1 : u ≠ 1) (i : Fin d.r) :
    ∃ k ∈ d.K i, u * k * u⁻¹ ≠ k := by
  have hex : ∃ j, ∃ k ∈ d.K j, u * k * u⁻¹ ≠ k := by
    by_contra hcon
    push Not at hcon
    exact hu1 (d.faithful u hu hcon)
  obtain ⟨j, k, hk, hne⟩ := hex
  obtain ⟨β, hβ, hβj⟩ := d.trans j i
  have hk' : β * k * β⁻¹ ∈ d.K i := by
    have := d.σ_conj β hβ j k hk
    rwa [hβj] at this
  refine ⟨β * k * β⁻¹, hk', ?_⟩
  intro heq
  have huβ : u * β = β * u := api_comm hB hu hβ
  have h1 : u * (β * k * β⁻¹) * u⁻¹ = β * (u * k * u⁻¹) * β⁻¹ := by
    calc u * (β * k * β⁻¹) * u⁻¹ = (u * β) * k * (u * β)⁻¹ := by simp [mul_assoc]
      _ = (β * u) * k * (β * u)⁻¹ := by rw [huβ]
      _ = β * (u * k * u⁻¹) * β⁻¹ := by simp [mul_assoc]
  rw [h1] at heq
  have h2 : β * (u * k * u⁻¹) = β * k := mul_right_cancel heq
  exact hne (mul_left_cancel h2)

def Delta (b : G) (i : Fin d.r) : Subgroup G where
  carrier := {c | c ∈ X ∧ b * c * b⁻¹ = c ∧
    ∀ j, (∀ m < p, (d.σ b ^ m) i ≠ j) → d.π j c = 1}
  mul_mem' := by
    intro x y hx hy
    refine ⟨X.mul_mem hx.1 hy.1, ?_, ?_⟩
    · calc b * (x * y) * b⁻¹ = (b * x * b⁻¹) * (b * y * b⁻¹) := by group
        _ = x * y := by rw [hx.2.1, hy.2.1]
    · intro j hj
      rw [d.π_mul j x hx.1 y hy.1, hx.2.2 j hj, hy.2.2 j hj, mul_one]
  one_mem' := by
    refine ⟨X.one_mem, by simp, ?_⟩
    intro j _
    have h := d.π_mul j 1 X.one_mem 1 X.one_mem
    simp only [mul_one] at h
    have h2 : d.π j 1 * d.π j 1 = d.π j 1 * 1 := by rw [mul_one, ← h]
    exact mul_left_cancel h2
  inv_mem' := by
    intro x hx
    refine ⟨X.inv_mem hx.1, ?_, ?_⟩
    · calc b * x⁻¹ * b⁻¹ = (b * x * b⁻¹)⁻¹ := by group
        _ = x⁻¹ := by rw [hx.2.1]
    · intro j hj
      have h := d.π_mul j x⁻¹ (X.inv_mem hx.1) x hx.1
      rw [inv_mul_cancel, hx.2.2 j hj, mul_one] at h
      have h1 := d.π_mul j 1 X.one_mem 1 X.one_mem
      simp only [mul_one] at h1
      have h2 : d.π j 1 * d.π j 1 = d.π j 1 * 1 := by rw [mul_one, ← h1]
      have h3 : d.π j 1 = 1 := mul_left_cancel h2
      rw [h3] at h
      exact h.symm

theorem Delta_le_X (b : G) (i : Fin d.r) : d.Delta b i ≤ X := fun _ hc => hc.1

theorem Delta_le_cent (b : G) (i : Fin d.r) :
    d.Delta b i ≤ Subgroup.centralizer ({b} : Set G) := by
  intro c hc
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := hc.2.1
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h.symm

private theorem api_π_one (j : Fin d.r) : d.π j 1 = 1 := by
  have h := d.π_mul j 1 X.one_mem 1 X.one_mem
  simp only [mul_one] at h
  have h2 : d.π j 1 * d.π j 1 = d.π j 1 * 1 := by rw [mul_one, ← h]
  exact mul_left_cancel h2

theorem exists_Delta (hp : p.Prime) (hB : IsElemAbelian p B) {b : G} (hb : b ∈ B) {i : Fin d.r}
    (hbi : d.σ b i ≠ i) {k : G} (hk : k ∈ d.K i) : ∃ c ∈ d.Delta b i, d.π i c = k := by
  classical
  set s := d.σ b with hs
  have hp0 : 0 < p := hp.pos
  have hsp : s ^ p = 1 := by
    rw [hs, ← d.σ_pow hb p, hB.2 b hb, d.σ_one]
  have hbp : b ^ p = 1 := hB.2 b hb
  have hinj : ∀ m n, m < p → n < p → (s ^ m) i = (s ^ n) i → m = n := by
    have key : ∀ m n, m < n → n < p → (s ^ m) i = (s ^ n) i → False := by
      intro m n hmn hn heq
      have h1 : (s ^ n) i = (s ^ m) ((s ^ (n - m)) i) := by
        rw [← Equiv.Perm.mul_apply, ← pow_add]
        congr 2
        omega
      rw [h1] at heq
      have h2 : (s ^ (n - m)) i = i := (s ^ m).injective heq.symm
      exact d.orbit_free hp hB hb hbi (by omega) (by omega) h2
    intro m n hm hn heq
    rcases lt_trichotomy m n with h | h | h
    · exact (key m n h hn heq).elim
    · exact h
    · exact (key n m h hm heq.symm).elim
  let Q : Fin d.r → Prop := fun j => ∃ m < p, (s ^ m) i = j
  let f : Fin d.r → G := fun j =>
    if h : Q j then b ^ (Classical.choose h) * k * (b ^ (Classical.choose h))⁻¹ else 1
  have f_orb : ∀ m < p, f ((s ^ m) i) = b ^ m * k * (b ^ m)⁻¹ := by
    intro m hm
    have hQ : Q ((s ^ m) i) := ⟨m, hm, rfl⟩
    have hspec := Classical.choose_spec hQ
    have : Classical.choose hQ = m := hinj _ _ hspec.1 hm hspec.2
    simp only [f, hQ, ↓reduceDIte, this]
  have f_not : ∀ j, ¬ Q j → f j = 1 := by
    intro j hj
    simp only [f, hj, ↓reduceDIte]
  have f_mem : ∀ j, f j ∈ d.K j := by
    intro j
    by_cases hj : Q j
    · obtain ⟨m, hm, rfl⟩ := hj
      rw [f_orb m hm]
      have := d.σ_conj (b ^ m) (B.pow_mem hb m) i k hk
      rwa [d.σ_pow hb m] at this
    · rw [f_not j hj]
      exact (d.K j).one_mem
  have Q_s : ∀ j, Q (s j) ↔ Q j := by
    intro j
    constructor
    · rintro ⟨m, hm, hmj⟩
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        refine ⟨p - 1, by omega, ?_⟩
        have h1 : i = s j := by simpa using hmj
        have h2 : (s ^ (p - 1)) i = j := by
          have h3 : s ^ (p - 1) * s = 1 := by
            rw [← pow_succ]
            have : p - 1 + 1 = p := by omega
            rw [this, hsp]
          have h4 : (s ^ (p - 1) * s) j = j := by rw [h3]; rfl
          rw [h1]
          exact h4
        exact h2
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        refine ⟨m', by omega, ?_⟩
        have : s ((s ^ m') i) = s j := by
          rw [← hmj, pow_succ']; rfl
        exact s.injective this
    · rintro ⟨m, hm, rfl⟩
      by_cases hm1 : m + 1 < p
      · exact ⟨m + 1, hm1, by rw [pow_succ']; rfl⟩
      · refine ⟨0, hp0, ?_⟩
        have : m + 1 = p := by omega
        have h5 : s ((s ^ m) i) = i := by
          have : (s ^ (m + 1)) i = i := by rw [‹m + 1 = p›, hsp]; rfl
          rw [pow_succ'] at this
          exact this
        simp [h5]
  have key : ∀ j, b * f j * b⁻¹ = f (s j) := by
    intro j
    by_cases hj : Q j
    · obtain ⟨m, hm, rfl⟩ := hj
      rw [f_orb m hm]
      have hsj : s ((s ^ m) i) = (s ^ (m + 1)) i := by rw [pow_succ']; rfl
      rw [hsj]
      by_cases hm1 : m + 1 < p
      · rw [f_orb (m + 1) hm1, pow_succ']
        group
      · have hmp : m + 1 = p := by omega
        have : (s ^ (m + 1)) i = (s ^ 0) i := by rw [hmp, hsp]; rfl
        rw [this, f_orb 0 hp0]
        have h6 : b * (b ^ m * k * (b ^ m)⁻¹) * b⁻¹ = b ^ (m + 1) * k * (b ^ (m + 1))⁻¹ := by
          rw [pow_succ']; group
        rw [h6, hmp, hbp]
        simp
    · have hj' : ¬ Q (s j) := fun h => hj ((Q_s j).1 h)
      rw [f_not j hj, f_not _ hj']
      simp
  obtain ⟨c, hcX, hc⟩ := d.exists_of_coord f f_mem
  have hbc : b * c * b⁻¹ = c := by
    apply d.π_ext _ (d.B_norm b hb c hcX) c hcX
    intro j'
    obtain ⟨j, rfl⟩ : ∃ j, s j = j' := ⟨s.symm j', by simp⟩
    rw [hc (s j), ← key j, ← hc j]
    exact d.π_conj b hb c hcX j
  refine ⟨c, ⟨hcX, hbc, ?_⟩, ?_⟩
  · intro j hj
    rw [hc j]
    apply f_not
    rintro ⟨m, hm, hmj⟩
    exact hj m hm hmj
  · rw [hc i]
    have := f_orb 0 hp0
    simpa using this

theorem Delta_inj {b : G} (hb : b ∈ B) {i : Fin d.r} {c c' : G} (hc : c ∈ d.Delta b i)
    (hc' : c' ∈ d.Delta b i) (h : d.π i c = d.π i c') : c = c' := by
  classical
  apply d.π_ext c hc.1 c' hc'.1
  intro j
  by_cases hj : ∃ m < p, (d.σ b ^ m) i = j
  · obtain ⟨m, _, rfl⟩ := hj
    rw [d.coord_pow hb hc.1 hc.2.1 i m, d.coord_pow hb hc'.1 hc'.2.1 i m, h]
  · push Not at hj
    rw [hc.2.2 j hj, hc'.2.2 j hj]

theorem cent_ne_bot (hp : p.Prime) (hB : IsElemAbelian p B) {b : G} (hb : b ∈ B)
    (hmove : ∃ i, d.σ b i ≠ i) : X ⊓ Subgroup.centralizer ({b} : Set G) ≠ ⊥ := by
  obtain ⟨i, hi⟩ := hmove
  obtain ⟨a, a', haa⟩ := d.K_nonab i
  have ha1 : a.1 ≠ 1 := by
    intro h
    apply haa
    have : a = 1 := Subtype.ext h
    rw [this]; simp
  obtain ⟨c, hc, hci⟩ := d.exists_Delta hp hB hb hi a.2
  intro hbot
  have hmem : c ∈ X ⊓ Subgroup.centralizer ({b} : Set G) :=
    ⟨d.Delta_le_X b i hc, d.Delta_le_cent b i hc⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [hmem, d.api_π_one] at hci
  exact ha1 hci.symm

end FactorData

end NonabelianAPI

section NonabelianCore

namespace FactorData

variable {p : ℕ} {G : Type} [Group G] {B X : Subgroup G} (d : FactorData p G B X)

section N2

open scoped commutatorElement

theorem n2_comm_B {B : Subgroup G} (hB : IsElemAbelian p B) {a b : G} (ha : a ∈ B) (hb : b ∈ B) :
    a * b = b * a := CFSG.Open.IsElemAbelian.comm hB ha hb

theorem n2_pow_conj {b c : G} (h : b * c * b⁻¹ = c) (m : ℕ) : b ^ m * c * (b ^ m)⁻¹ = c := by
  have hc : Commute b c := mul_inv_eq_iff_eq_mul.mp h
  exact (Commute.pow_left hc m).mul_inv_cancel

theorem n2_mem_C {X : Subgroup G} {b c : G} :
    c ∈ X ⊓ Subgroup.centralizer ({b} : Set G) ↔ c ∈ X ∧ b * c * b⁻¹ = c := by
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [mul_inv_eq_iff_eq_mul]

theorem n2_comm_mul_of_comm {a x w : G} (h : a * w = w * a) : ⁅a, x * w⁆ = ⁅a, x⁆ := by
  have h' : a * w * a⁻¹ = w := by rw [h]; group
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (x * w) * a⁻¹ * (x * w)⁻¹ = (a * x * a⁻¹) * (a * w * a⁻¹) * w⁻¹ * x⁻¹ := by group
    _ = a * x * a⁻¹ * x⁻¹ := by rw [h']; group

theorem n2_orbit_mem {α : Type*} {s : Equiv.Perm α} {p : ℕ} (hp : 0 < p) (hs : s ^ p = 1)
    {x y : α} {n m : ℕ} (h : (s ^ n) x = (s ^ m) y) : ∃ k < p, (s ^ k) y = x := by
  refine ⟨(n * (p - 1) + m) % p, Nat.mod_lt _ hp, ?_⟩
  rw [← pow_eq_pow_mod _ hs, pow_add, Equiv.Perm.mul_apply, ← h, ← Equiv.Perm.mul_apply,
    ← pow_add]
  have : n * (p - 1) + n = p * n := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp [Nat.mul_comm, Nat.mul_add]
  rw [this, pow_mul, hs, one_pow]
  rfl

theorem n2_π_one (i : Fin d.r) : d.π i 1 = 1 := d.π_self i 1 (one_mem _)

theorem n2_π_inv (i : Fin d.r) {g : G} (hg : g ∈ X) : d.π i g⁻¹ = (d.π i g)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← d.π_mul i _ (inv_mem hg) _ hg, inv_mul_cancel, n2_π_one]

theorem n2_π_comm (i : Fin d.r) {g h : G} (hg : g ∈ X) (hh : h ∈ X) :
    d.π i ⁅g, h⁆ = ⁅d.π i g, d.π i h⁆ := by
  rw [commutatorElement_def, commutatorElement_def,
    d.π_mul i _ (mul_mem (mul_mem hg hh) (inv_mem hg)) _ (inv_mem hh),
    d.π_mul i _ (mul_mem hg hh) _ (inv_mem hg), d.π_mul i _ hg _ hh,
    n2_π_inv d i hg, n2_π_inv d i hh]

@[expose] def n2_img (i : Fin d.r) (T : Subgroup G) (hT : T ≤ X) : Subgroup G where
  carrier := {k | ∃ t ∈ T, d.π i t = k}
  mul_mem' := by
    rintro _ _ ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩
    exact ⟨t * t', mul_mem ht ht', d.π_mul i t (hT ht) t' (hT ht')⟩
  one_mem' := ⟨1, one_mem _, n2_π_one d i⟩
  inv_mem' := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t⁻¹, inv_mem ht, n2_π_inv d i (hT ht)⟩

theorem n2_Delta_perfect (hp : p.Prime) (hB : IsElemAbelian p B) {b : G} (hb : b ∈ B)
    {i : Fin d.r} (hbi : d.σ b i ≠ i) : d.Delta b i ≤ ⁅d.Delta b i, d.Delta b i⁆ := by
  have hPΔ : ⁅d.Delta b i, d.Delta b i⁆ ≤ d.Delta b i := by
    rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  have hPX : ⁅d.Delta b i, d.Delta b i⁆ ≤ X := hPΔ.trans (d.Delta_le_X b i)
  have hK : d.K i ≤ n2_img d i ⁅d.Delta b i, d.Delta b i⁆ hPX := by
    rw [← d.K_perfect i, Subgroup.commutator_le]
    intro k' hk' k hk
    obtain ⟨c₁, hc₁, rfl⟩ := d.exists_Delta hp hB hb hbi hk'
    obtain ⟨c₂, hc₂, rfl⟩ := d.exists_Delta hp hB hb hbi hk
    exact ⟨⁅c₁, c₂⁆, Subgroup.commutator_mem_commutator hc₁ hc₂,
      n2_π_comm d i (d.Delta_le_X b i hc₁) (d.Delta_le_X b i hc₂)⟩
  intro c hc
  obtain ⟨t, ht, hti⟩ := hK (d.π_mem i c (d.Delta_le_X b i hc))
  have := d.Delta_inj hb (hPΔ ht) hc hti
  rw [← this]
  exact ht

theorem n2_Delta_conj (hB : IsElemAbelian p B) {b u : G} (hb : b ∈ B) (hu : u ∈ B)
    {i : Fin d.r} (hui : d.σ u i = i) {c : G} (hc : c ∈ d.Delta b i) :
    u * c * u⁻¹ ∈ d.Delta b i := by
  refine ⟨d.B_norm u hu c hc.1, ?_, ?_⟩
  · have hbu : b * u = u * b := n2_comm_B hB hb hu
    calc b * (u * c * u⁻¹) * b⁻¹ = (b * u) * c * (b * u)⁻¹ := by group
      _ = (u * b) * c * (u * b)⁻¹ := by rw [hbu]
      _ = u * (b * c * b⁻¹) * u⁻¹ := by group
      _ = u * c * u⁻¹ := by rw [hc.2.1]
  · intro j hj
    have h1 := d.π_conj u hu c hc.1 j
    rw [d.stab_all hB hu hui (j := j), hc.2.2 j hj] at h1
    simpa using h1

theorem n2_Delta_le (hp : p.Prime) (hB : IsElemAbelian p B) {b u : G} (hb : b ∈ B) (hu : u ∈ B)
    {i : Fin d.r} (hbi : d.σ b i ≠ i) (hui : d.σ u i = i) (hu1 : u ≠ 1)
    {T : Subgroup G} (hTΔ : T ≤ d.Delta b i)
    (hTn : ∀ c ∈ d.Delta b i, ∀ t ∈ T, c * t * c⁻¹ ∈ T)
    (hTc : ∀ c ∈ d.Delta b i, c⁻¹ * (u * c * u⁻¹) ∈ T) : d.Delta b i ≤ T := by
  have hTX : T ≤ X := hTΔ.trans (d.Delta_le_X b i)
  have : IsSimpleGroup ↥(d.K i) := d.K_simple i
  have hnorm : ((n2_img d i T hTX).subgroupOf (d.K i)).Normal := by
    refine ⟨?_⟩
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨t, ht, htn⟩ := hn
    obtain ⟨c, hc, hci⟩ := d.exists_Delta hp hB hb hbi g.2
    refine ⟨c * t * c⁻¹, hTn c hc t ht, ?_⟩
    have hcX := d.Delta_le_X b i hc
    have htX := hTX ht
    rw [d.π_mul i _ (mul_mem hcX htX) _ (inv_mem hcX), d.π_mul i _ hcX _ htX,
      n2_π_inv d i hcX, hci]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [htn]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((n2_img d i T hTX).subgroupOf (d.K i)) with hbot | htop
  · exfalso
    obtain ⟨k₀, hk₀, hk₀ne⟩ := d.moves_all hB hu hu1 i
    obtain ⟨c₀, hc₀, hc₀i⟩ := d.exists_Delta hp hB hb hbi hk₀
    have hc₀X := d.Delta_le_X b i hc₀
    have hs₀ := hTc c₀ hc₀
    have huc₀X : u * c₀ * u⁻¹ ∈ X := d.B_norm u hu c₀ hc₀X
    have hπ : d.π i (c₀⁻¹ * (u * c₀ * u⁻¹)) = k₀⁻¹ * (u * k₀ * u⁻¹) := by
      rw [d.π_mul i _ (inv_mem hc₀X) _ huc₀X, n2_π_inv d i hc₀X, hc₀i]
      have h1 := d.π_conj u hu c₀ hc₀X i
      rw [hui, hc₀i] at h1
      rw [h1]
    have hmem : (⟨k₀⁻¹ * (u * k₀ * u⁻¹), mul_mem (inv_mem hk₀)
        (by have h := d.σ_conj u hu i k₀ hk₀; rwa [hui] at h)⟩ : ↥(d.K i)) ∈
        (n2_img d i T hTX).subgroupOf (d.K i) := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨_, hs₀, hπ⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hk₀ne
    have := congrArg Subtype.val hmem
    simp only [OneMemClass.coe_one] at this
    exact (inv_mul_eq_one.mp this).symm
  · intro c hc
    have hmem : (⟨d.π i c, d.π_mem i c (d.Delta_le_X b i hc)⟩ : ↥(d.K i)) ∈
        (n2_img d i T hTX).subgroupOf (d.K i) := by
      rw [htop]; exact Subgroup.mem_top _
    rw [Subgroup.mem_subgroupOf] at hmem
    obtain ⟨t, ht, hti⟩ := hmem
    rw [← d.Delta_inj hb (hTΔ ht) hc hti]
    exact ht

theorem n2_Delta_comm_le (hp : p.Prime) (hB : IsElemAbelian p B) {b e : G} (hb : b ∈ B)
    (he : e ∈ B) {i : Fin d.r} (hbi : d.σ b i ≠ i) (hi' : ∀ m < p, (d.σ b ^ m) i ≠ d.σ e i)
    {M : Subgroup G}
    (hM : ∀ c ∈ d.Delta b i, c⁻¹ * (e * c * e⁻¹) ∈ M)
    (hMn : ∀ c' ∈ d.Delta b i, ∀ m ∈ M, ⁅c', m⁆ ∈ M) : d.Delta b i ≤ M := by
  have hs : d.σ b ^ p = 1 := by
    rw [← d.σ_pow hb p, hB.2 b hb, d.σ_one]
  have hcomm : ∀ n : ℕ, d.σ b ^ n * d.σ e = d.σ e * d.σ b ^ n := fun n =>
    (Commute.pow_left (show Commute (d.σ b) (d.σ e) from d.σ_comm hB hb he) n).eq
  have hcc : ∀ c' ∈ d.Delta b i, ∀ c ∈ d.Delta b i,
      c' * (e * c * e⁻¹) = (e * c * e⁻¹) * c' := by
    intro c' hc' c hc
    have hw : e * c * e⁻¹ ∈ X := d.B_norm e he c hc.1
    apply d.π_ext _ (mul_mem (d.Delta_le_X b i hc') hw) _ (mul_mem hw (d.Delta_le_X b i hc'))
    intro j
    rw [d.π_mul j _ (d.Delta_le_X b i hc') _ hw, d.π_mul j _ hw _ (d.Delta_le_X b i hc')]
    by_cases hj : ∃ m < p, (d.σ b ^ m) i = j
    · have h1 : d.π j (e * c * e⁻¹) = 1 := by
        obtain ⟨m, hm, rfl⟩ := hj
        obtain ⟨j₀, hj₀⟩ := (d.σ e).surjective ((d.σ b ^ m) i)
        have h2 := d.π_conj e he c hc.1 j₀
        rw [hj₀] at h2
        have h3 : d.π j₀ c = 1 := by
          apply hc.2.2 j₀
          intro n hn hnj
          have h4 : (d.σ b ^ n) (d.σ e i) = (d.σ b ^ m) i := by
            rw [← hj₀, ← hnj]
            exact congrArg (fun f => f i) (hcomm n)
          obtain ⟨k, hk, hki⟩ := n2_orbit_mem hp.pos hs h4
          exact hi' k hk hki
        rw [h2, h3]; simp
      rw [h1]; simp
    · have h1 : d.π j c' = 1 := hc'.2.2 j (by
        intro m hm hmj; exact hj ⟨m, hm, hmj⟩)
      rw [h1]; simp
  have hΔ2 : ⁅d.Delta b i, d.Delta b i⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro c₁ hc₁ c₂ hc₂
    have h1 := hMn c₁ hc₁ _ (hM c₂⁻¹ (inv_mem hc₂))
    rw [inv_inv, n2_comm_mul_of_comm (hcc c₁ hc₁ c₂⁻¹ (inv_mem hc₂))] at h1
    exact h1
  exact (n2_Delta_perfect d hp hB hb hbi).trans hΔ2

theorem cent_le_comm (hp : p.Prime) (hB : IsElemAbelian p B) {b e : G} (hb : b ∈ B) (he : e ∈ B)
    (hmove : ∃ i, d.σ b i ≠ i) (heb : e ∉ Subgroup.zpowers b) :
    X ⊓ Subgroup.centralizer ({b} : Set G) ≤
      ⁅X ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers e⁆ := by
  classical
  set C := X ⊓ Subgroup.centralizer ({b} : Set G) with hC
  set M := ⁅C, Subgroup.zpowers e⁆ with hMdef
  have hall : ∀ i, d.σ b i ≠ i := fun i h => by
    obtain ⟨j, hj⟩ := hmove
    exact hj (d.stab_all hB hb h)
  have hDC : ∀ i, d.Delta b i ≤ C := fun i c hc => n2_mem_C.mpr ⟨hc.1, hc.2.1⟩
  have hMn : ∀ c ∈ C, ∀ m ∈ M, c * m * c⁻¹ ∈ M := by
    intro c hc
    have hle : M ≤ M.comap (MulAut.conj c).toMonoidHom := by
      rw [hMdef, Subgroup.commutator_le]
      intro c' hc' e' he'
      rw [Subgroup.mem_comap]
      have h1 : (MulAut.conj c).toMonoidHom ⁅c', e'⁆ = ⁅c * c', e'⁆ * ⁅c, e'⁆⁻¹ := by
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
        simp only [commutatorElement_def]
        group
      rw [h1]
      exact mul_mem (Subgroup.commutator_mem_commutator (mul_mem hc hc') he')
        (inv_mem (Subgroup.commutator_mem_commutator hc he'))
    intro m hm
    exact hle hm
  have hMc : ∀ c' ∈ C, ∀ m ∈ M, ⁅c', m⁆ ∈ M := by
    intro c' hc' m hm
    rw [commutatorElement_def]
    exact mul_mem (hMn c' hc' m hm) (inv_mem hm)
  have hΔ : ∀ i, d.Delta b i ≤ M := by
    intro i
    have hbi := hall i
    have hMmem : ∀ c ∈ d.Delta b i, c⁻¹ * (e * c * e⁻¹) ∈ M := by
      intro c hc
      have := Subgroup.commutator_mem_commutator (inv_mem (hDC i hc)) (Subgroup.mem_zpowers e)
      simpa [commutatorElement_def, mul_assoc] using this
    by_cases hQ : ∃ j < p, (d.σ b ^ j) i = d.σ e i
    · obtain ⟨j, hj, hji⟩ := hQ
      obtain ⟨u, hu_def⟩ : ∃ u : G, u = e * (b ^ j)⁻¹ := ⟨_, rfl⟩
      have hbj : b ^ j ∈ B := pow_mem hb j
      have hu : u ∈ B := by rw [hu_def]; exact mul_mem he (inv_mem hbj)
      have heu : e = u * b ^ j := by rw [hu_def]; group
      have hui : d.σ u i = i := by
        have h1 : d.σ e = d.σ u * d.σ (b ^ j) := by rw [← d.σ_mul u hu _ hbj, ← heu]
        have hc := d.σ_comm hB hu hbj
        have h3 : d.σ e i = (d.σ b ^ j) (d.σ u i) := by
          rw [h1, hc, d.σ_pow hb j]; rfl
        exact (d.σ b ^ j).injective (h3.symm.trans hji.symm)
      have hu1 : u ≠ 1 := by
        intro h
        apply heb
        rw [heu, h, one_mul]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers b) j
      have hconj : ∀ c ∈ d.Delta b i, e * c * e⁻¹ = u * c * u⁻¹ := by
        intro c hc
        rw [heu]
        calc u * b ^ j * c * (u * b ^ j)⁻¹ = u * (b ^ j * c * (b ^ j)⁻¹) * u⁻¹ := by group
          _ = u * c * u⁻¹ := by rw [n2_pow_conj hc.2.1 j]
      have hTn : ∀ c ∈ d.Delta b i, ∀ t ∈ M ⊓ d.Delta b i, c * t * c⁻¹ ∈ M ⊓ d.Delta b i := by
        intro c hc t ht
        exact ⟨hMn c (hDC i hc) t ht.1,
          (d.Delta b i).mul_mem ((d.Delta b i).mul_mem hc ht.2) ((d.Delta b i).inv_mem hc)⟩
      have hTc : ∀ c ∈ d.Delta b i, c⁻¹ * (u * c * u⁻¹) ∈ M ⊓ d.Delta b i := by
        intro c hc
        refine ⟨?_, (d.Delta b i).mul_mem ((d.Delta b i).inv_mem hc) (n2_Delta_conj d hB hb hu hui hc)⟩
        rw [← hconj c hc]
        exact hMmem c hc
      have := d.n2_Delta_le hp hB hb hu hbi hui hu1 (T := M ⊓ d.Delta b i) inf_le_right hTn hTc
      intro c hc
      exact (this hc).1
    · push Not at hQ
      exact d.n2_Delta_comm_le hp hB hb he hbi hQ hMmem
        (fun c' hc' m hm => hMc c' (hDC i hc') m hm)
  have key : ∀ n : ℕ, ∀ c ∈ C, (Finset.univ.filter (fun j => d.π j c ≠ 1)).card = n → c ∈ M := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro c hc hn
      obtain ⟨hcX, hcb⟩ := n2_mem_C.mp hc
      by_cases h0 : ∃ i, d.π i c ≠ 1
      · obtain ⟨i, hi⟩ := h0
        obtain ⟨c', hc'Δ, hc'i⟩ := d.exists_Delta hp hB hb (hall i) (d.π_mem i c hcX)
        have hc'X := d.Delta_le_X b i hc'Δ
        have hc'b := hc'Δ.2.1
        have hc''C : c * c'⁻¹ ∈ C := by
          refine n2_mem_C.mpr ⟨mul_mem hcX (inv_mem hc'X), ?_⟩
          calc b * (c * c'⁻¹) * b⁻¹ = (b * c * b⁻¹) * (b * c' * b⁻¹)⁻¹ := by group
            _ = c * c'⁻¹ := by rw [hcb, hc'b]
        have hcoord : ∀ m : ℕ, d.π ((d.σ b ^ m) i) (c * c'⁻¹) = 1 := by
          intro m
          rw [d.π_mul _ c hcX c'⁻¹ (inv_mem hc'X), n2_π_inv d _ hc'X, d.coord_pow hb hcX hcb,
            d.coord_pow hb hc'X hc'b, hc'i]
          simp
        have hsub : Finset.univ.filter (fun j => d.π j (c * c'⁻¹) ≠ 1) ⊂
            Finset.univ.filter (fun j => d.π j c ≠ 1) := by
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨i, by simpa using hi, ?_⟩
            have h0 := hcoord 0
            simp only [pow_zero, Equiv.Perm.coe_one, id_eq] at h0
            simp [h0]
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
            have hjQ : ∀ m < p, (d.σ b ^ m) i ≠ j := by
              intro m hm hmj; apply hj; rw [← hmj]; exact hcoord m
            have h1 := hc'Δ.2.2 j hjQ
            rw [d.π_mul _ c hcX c'⁻¹ (inv_mem hc'X), n2_π_inv d _ hc'X, h1] at hj
            simpa using hj
        have h1 := ih _ (lt_of_lt_of_eq (Finset.card_lt_card hsub) hn) (c * c'⁻¹) hc''C rfl
        have h2 := mul_mem h1 (hΔ i hc'Δ)
        simpa using h2
      · push Not at h0
        have : c = 1 := d.π_ext c hcX 1 (one_mem _) (fun i => by rw [h0 i, n2_π_one])
        rw [this]; exact one_mem _
  intro c hc
  exact key _ c hc rfl

end N2

@[expose] noncomputable def maxl_supp (y : G) : Finset (Fin d.r) :=
  open Classical in Finset.univ.filter (fun j => d.π j y ≠ 1)

theorem maxl_mem_supp (y : G) (j : Fin d.r) : j ∈ d.maxl_supp y ↔ d.π j y ≠ 1 := by
  simp [maxl_supp]

@[expose] def maxl_Q (b : G) (i : Fin d.r) : Finset (Fin d.r) :=
  (Finset.range p).image (fun m => (d.σ b ^ m) i)

theorem maxl_mem_Q (b : G) (i j : Fin d.r) :
    j ∈ d.maxl_Q b i ↔ ∃ m < p, (d.σ b ^ m) i = j := by
  simp [maxl_Q]

@[expose] def maxl_MinSupp (Y : Subgroup G) (S : Finset (Fin d.r)) : Prop :=
  (∃ y ∈ Y, y ≠ 1 ∧ d.maxl_supp y = S) ∧ ∀ y ∈ Y, y ≠ 1 → S.card ≤ (d.maxl_supp y).card

theorem maxl_π_one (j : Fin d.r) : d.π j 1 = 1 := d.π_self j 1 (one_mem _)

theorem maxl_π_inv {g : G} (hg : g ∈ X) (j : Fin d.r) : d.π j g⁻¹ = (d.π j g)⁻¹ := by
  have h := d.π_mul j g hg g⁻¹ (inv_mem hg)
  rw [mul_inv_cancel, maxl_π_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem maxl_π_conj_X {y t : G} (hy : y ∈ X) (ht : t ∈ X) (j : Fin d.r) :
    d.π j (y * t * y⁻¹) = d.π j y * d.π j t * (d.π j y)⁻¹ := by
  rw [d.π_mul j (y * t) (mul_mem hy ht) y⁻¹ (inv_mem hy), d.π_mul j y hy t ht,
    maxl_π_inv d hy]

theorem maxl_π_comm_X {u s : G} (hu : u ∈ X) (hs : s ∈ X) (j : Fin d.r) :
    d.π j (u * s * u⁻¹ * s⁻¹) = d.π j u * d.π j s * (d.π j u)⁻¹ * (d.π j s)⁻¹ := by
  rw [d.π_mul j (u * s * u⁻¹) (mul_mem (mul_mem hu hs) (inv_mem hu)) s⁻¹ (inv_mem hs),
    maxl_π_conj_X d hu hs, maxl_π_inv d hs]

theorem maxl_π_mul_inv_X {y t : G} (hy : y ∈ X) (ht : t ∈ X) (j : Fin d.r) :
    d.π j (y * t⁻¹) = d.π j y * (d.π j t)⁻¹ := by
  rw [d.π_mul j y hy t⁻¹ (inv_mem ht), maxl_π_inv d ht]

theorem maxl_simple_normal (i : Fin d.r) (N : Subgroup G) (hN : N ≤ d.K i)
    (hnorm : ∀ k ∈ d.K i, ∀ n ∈ N, k * n * k⁻¹ ∈ N) : N = ⊥ ∨ d.K i ≤ N := by
  have := d.K_simple i
  have hn : (N.subgroupOf (d.K i)).Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm k k.2 n hn
  have := hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (d.K i)) with h | h
  · left
    rw [Subgroup.eq_bot_iff_forall]
    intro n hn'
    have : (⟨n, hN hn'⟩ : d.K i) ∈ N.subgroupOf (d.K i) := hn'
    rw [h, Subgroup.mem_bot] at this
    simpa using congrArg Subtype.val this
  · right
    exact Subgroup.subgroupOf_eq_top.1 h

theorem maxl_D_i {Y : Subgroup G} {S : Finset (Fin d.r)} (hS : d.maxl_MinSupp Y S)
    {t : G} (htY : t ∈ Y) (ht1 : t ≠ 1) (htS : ∀ j, j ∉ S → d.π j t = 1) :
    d.maxl_supp t = S := by
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    by_contra h
    exact (d.maxl_mem_supp t j).1 hj (htS j h)
  · exact hS.2 t htY ht1

theorem maxl_D_ii {Y : Subgroup G} {S : Finset (Fin d.r)} (hS : d.maxl_MinSupp Y S)
    {i : Fin d.r} (hi : i ∈ S) {t : G} (htY : t ∈ Y) (htS : ∀ j, j ∉ S → d.π j t = 1)
    (hti : d.π i t = 1) : t = 1 := by
  by_contra ht1
  have h := d.maxl_D_i hS htY ht1 htS
  have hi' : i ∈ d.maxl_supp t := h ▸ hi
  exact (d.maxl_mem_supp t i).1 hi' hti

theorem maxl_D_iii {Y : Subgroup G} (hYX : Y ≤ X)
    (hcov : ∀ i, ∀ k ∈ d.K i, ∃ y ∈ Y, d.π i y = k)
    {S : Finset (Fin d.r)} (hS : d.maxl_MinSupp Y S)
    {i : Fin d.r} (hi : i ∈ S) {k : G} (hk : k ∈ d.K i) :
    ∃ t ∈ Y, (∀ j, j ∉ S → d.π j t = 1) ∧ d.π i t = k := by
  let N : Subgroup G :=
    { carrier := {k | ∃ t ∈ Y, (∀ j, j ∉ S → d.π j t = 1) ∧ d.π i t = k}
      mul_mem' := by
        rintro _ _ ⟨t, htY, htS, rfl⟩ ⟨t', ht'Y, ht'S, rfl⟩
        refine ⟨t * t', mul_mem htY ht'Y, fun j hj => ?_, ?_⟩
        · rw [d.π_mul j t (hYX htY) t' (hYX ht'Y), htS j hj, ht'S j hj, one_mul]
        · exact d.π_mul i t (hYX htY) t' (hYX ht'Y)
      one_mem' := ⟨1, one_mem _, fun j _ => d.maxl_π_one j, d.maxl_π_one i⟩
      inv_mem' := by
        rintro _ ⟨t, htY, htS, rfl⟩
        refine ⟨t⁻¹, inv_mem htY, fun j hj => ?_, ?_⟩
        · rw [d.maxl_π_inv (hYX htY), htS j hj, inv_one]
        · exact d.maxl_π_inv (hYX htY) i }
  have hNK : N ≤ d.K i := by
    rintro _ ⟨t, htY, _, rfl⟩
    exact d.π_mem i t (hYX htY)
  have hnorm : ∀ k ∈ d.K i, ∀ n ∈ N, k * n * k⁻¹ ∈ N := by
    intro k' hk' n hn
    obtain ⟨t, htY, htS, rfl⟩ := hn
    obtain ⟨y, hyY, rfl⟩ := hcov i k' hk'
    refine ⟨y * t * y⁻¹, mul_mem (mul_mem hyY htY) (inv_mem hyY), fun j hj => ?_, ?_⟩
    · rw [d.maxl_π_conj_X (hYX hyY) (hYX htY), htS j hj]; simp
    · exact d.maxl_π_conj_X (hYX hyY) (hYX htY) i
  rcases d.maxl_simple_normal i N hNK hnorm with h | h
  · exfalso
    obtain ⟨y₀, hy₀Y, hy₀1, hy₀S⟩ := hS.1
    have hmem : d.π i y₀ ∈ N := by
      refine ⟨y₀, hy₀Y, fun j hj => ?_, rfl⟩
      by_contra hne
      exact hj (hy₀S ▸ (d.maxl_mem_supp y₀ j).2 hne)
    rw [h, Subgroup.mem_bot] at hmem
    exact (d.maxl_mem_supp y₀ i).1 (hy₀S ▸ hi) hmem
  · exact h hk

theorem maxl_D_iv {Y : Subgroup G} (hYX : Y ≤ X)
    (hcov : ∀ i, ∀ k ∈ d.K i, ∃ y ∈ Y, d.π i y = k)
    {S : Finset (Fin d.r)} (hS : d.maxl_MinSupp Y S)
    {i : Fin d.r} (hi : i ∈ S) {y : G} (hyY : y ∈ Y) {t : G} (htY : t ∈ Y)
    (hti : d.π i t = d.π i y) :
    ∀ j ∈ S, d.π j y = d.π j t := by
  set u := y * t⁻¹ with hu
  have huY : u ∈ Y := mul_mem hyY (inv_mem htY)
  have huX : u ∈ X := hYX huY
  have hui : d.π i u = 1 := by
    rw [hu, d.maxl_π_mul_inv_X (hYX hyY) (hYX htY), hti, mul_inv_cancel]
  have hcomm : ∀ s ∈ Y, (∀ j, j ∉ S → d.π j s = 1) → u * s = s * u := by
    intro s hsY hsS
    have hsX : s ∈ X := hYX hsY
    have hw : u * s * u⁻¹ * s⁻¹ = 1 := by
      refine d.maxl_D_ii hS hi (mul_mem (mul_mem (mul_mem huY hsY) (inv_mem huY)) (inv_mem hsY))
        (fun j hj => ?_) ?_
      · rw [d.maxl_π_comm_X huX hsX, hsS j hj]; simp
      · rw [d.maxl_π_comm_X huX hsX, hui]; simp
    have : u * s = s * u := by
      calc u * s = (u * s * u⁻¹ * s⁻¹) * (s * u) := by group
        _ = s * u := by rw [hw, one_mul]
    exact this
  intro j hj
  have hz : d.π j u ∈ d.K j := d.π_mem j u huX
  have hz1 : d.π j u = 1 := by
    refine d.K_center j hz (fun k hk => ?_)
    obtain ⟨s, hsY, hsS, hsj⟩ := d.maxl_D_iii hYX hcov hS hj hk
    have := congrArg (d.π j) (hcomm s hsY hsS)
    rw [d.π_mul j u huX s (hYX hsY), d.π_mul j s (hYX hsY) u huX, hsj] at this
    exact this
  rw [hu, d.maxl_π_mul_inv_X (hYX hyY) (hYX htY)] at hz1
  exact mul_inv_eq_one.1 hz1

theorem maxl_D_v {Y : Subgroup G} (hYX : Y ≤ X)
    (hcov : ∀ i, ∀ k ∈ d.K i, ∃ y ∈ Y, d.π i y = k)
    {S : Finset (Fin d.r)} (hS : d.maxl_MinSupp Y S) {y₁ : G} (hy₁Y : y₁ ∈ Y)
    (hcard : (d.maxl_supp y₁).card ≤ S.card) {i : Fin d.r} (hi : i ∈ S)
    (hi' : i ∈ d.maxl_supp y₁) : d.maxl_supp y₁ = S := by
  have hk : d.π i y₁ ∈ d.K i := d.π_mem i y₁ (hYX hy₁Y)
  obtain ⟨t, htY, htS, hti⟩ := d.maxl_D_iii hYX hcov hS hi hk
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [d.maxl_π_one] at hti
    exact (d.maxl_mem_supp y₁ i).1 hi' hti.symm
  have hts := d.maxl_D_i hS htY ht1 htS
  have hdiv := d.maxl_D_iv hYX hcov hS hi hy₁Y htY hti
  have hsub : S ⊆ d.maxl_supp y₁ := by
    intro j hj
    rw [d.maxl_mem_supp, hdiv j hj]
    exact (d.maxl_mem_supp t j).1 (hts ▸ hj)
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

theorem maxl_exists_ne_one {y : G} (hy : y ∈ X) (hy1 : y ≠ 1) : ∃ j, d.π j y ≠ 1 := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hy1 (d.π_ext y hy 1 (one_mem _) (fun j => by rw [h j, d.maxl_π_one]))

theorem maxl_moves (hB : IsElemAbelian p B) {b : G} (hb : b ∈ B)
    (hmove : ∃ i, d.σ b i ≠ i) (j : Fin d.r) : d.σ b j ≠ j := by
  intro h
  obtain ⟨i, hi⟩ := hmove
  exact hi (d.stab_all hB hb h)

theorem maxl_Delta_van {b : G} {i : Fin d.r} {c : G} (hc : c ∈ d.Delta b i) {j : Fin d.r}
    (hj : j ∉ d.maxl_Q b i) : d.π j c = 1 :=
  hc.2.2 j (fun m hm h => hj ((d.maxl_mem_Q b i j).2 ⟨m, hm, h⟩))

theorem maxl_perm_pow_p (hB : IsElemAbelian p B) {b : G} (hb : b ∈ B) : d.σ b ^ p = 1 := by
  rw [← d.σ_pow hb, hB.2 b hb, d.σ_one]

theorem maxl_card_Q (hp : p.Prime) (hB : IsElemAbelian p B) {b : G} (hb : b ∈ B) {i : Fin d.r}
    (hbi : d.σ b i ≠ i) : (d.maxl_Q b i).card = p := by
  unfold maxl_Q
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro m hm m' hm' h
  simp only [Finset.coe_range, Set.mem_Iio] at hm hm'
  by_contra hne
  have key : ∀ m m' : ℕ, m < m' → m' < p → (d.σ b ^ m) i = (d.σ b ^ m') i → False := by
    intro m m' hlt hm' h
    have e : d.σ b ^ m' = d.σ b ^ m * d.σ b ^ (m' - m) := by
      rw [← pow_add]; congr 1; omega
    have h' : (d.σ b ^ m) i = (d.σ b ^ m) ((d.σ b ^ (m' - m)) i) := by
      rw [e] at h; exact h
    exact d.orbit_free hp hB hb hbi (m := m' - m) (by omega) (by omega)
      ((d.σ b ^ m).injective h').symm
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exact key m m' hlt hm' h
  · exact hne heq
  · exact key m' m hgt hm h.symm

theorem maxl_mem_supp_conj {β : G} (hβ : β ∈ B) {y : G} (hy : y ∈ X) (j : Fin d.r) :
    j ∈ d.maxl_supp (β * y * β⁻¹) ↔ (d.σ β).symm j ∈ d.maxl_supp y := by
  rw [d.maxl_mem_supp, d.maxl_mem_supp]
  have := d.π_conj β hβ y hy ((d.σ β).symm j)
  rw [Equiv.apply_symm_apply] at this
  rw [this]
  exact not_congr conj_eq_one_iff

theorem maxl_inv_pow (S : Finset (Fin d.r)) (e : Equiv.Perm (Fin d.r))
    (h : ∀ j, e j ∈ S ↔ j ∈ S) (m : ℕ) : ∀ j, (e ^ m) j ∈ S ↔ j ∈ S := by
  induction m with
  | zero => intro j; simp
  | succ m ih =>
    intro j
    rw [pow_succ, Equiv.Perm.mul_apply, ih, h]

theorem maxl_dichotomy {Y : Subgroup G} (hYX : Y ≤ X)
    (hBY : ∀ β ∈ B, ∀ y ∈ Y, β * y * β⁻¹ ∈ Y)
    (hcov : ∀ i, ∀ k ∈ d.K i, ∃ y ∈ Y, d.π i y = k)
    {S : Finset (Fin d.r)} (hS : d.maxl_MinSupp Y S) {β : G} (hβ : β ∈ B)
    (h : ∃ j ∈ S, d.σ β j ∈ S) : ∀ j, d.σ β j ∈ S ↔ j ∈ S := by
  obtain ⟨y₀, hy₀Y, hy₀1, hy₀S⟩ := hS.1
  have hy₁Y : β * y₀ * β⁻¹ ∈ Y := hBY β hβ y₀ hy₀Y
  have hmem : ∀ j, j ∈ d.maxl_supp (β * y₀ * β⁻¹) ↔ (d.σ β).symm j ∈ S := fun j => by
    rw [d.maxl_mem_supp_conj hβ (hYX hy₀Y), hy₀S]
  have hmap : d.maxl_supp (β * y₀ * β⁻¹) = S.map (d.σ β).toEmbedding := by
    ext j
    rw [hmem, Finset.mem_map_equiv]
  have hcard : (d.maxl_supp (β * y₀ * β⁻¹)).card ≤ S.card := by
    rw [hmap, Finset.card_map]
  obtain ⟨j₀, hj₀, hj₀'⟩ := h
  have hsupp := d.maxl_D_v hYX hcov hS hy₁Y hcard hj₀' (by rw [hmem]; simpa using hj₀)
  intro j
  have h1 : d.σ β j ∈ d.maxl_supp (β * y₀ * β⁻¹) ↔ d.σ β j ∈ S := by rw [hsupp]
  rw [← h1, hmem]
  simp

theorem maxl_E (hp : p.Prime) (hB : IsElemAbelian p B) {b : G} (hb : b ∈ B)
    (hmove : ∃ i, d.σ b i ≠ i) {Y : Subgroup G} (hYX : Y ≤ X)
    (hcov : ∀ i, ∀ k ∈ d.K i, ∃ y ∈ Y, d.π i y = k)
    (hCY : X ⊓ Subgroup.centralizer ({b} : Set G) ≤ Y)
    {S : Finset (Fin d.r)} (hS : d.maxl_MinSupp Y S) {i₀ : Fin d.r} (hi₀ : i₀ ∈ S) :
    ∀ j ∈ S, j ∈ d.maxl_Q b i₀ := by
  have hbi := d.maxl_moves hB hb hmove i₀
  obtain ⟨y₀, hy₀Y, hy₀1, hy₀S⟩ := hS.1
  obtain ⟨c, hc, hcπ⟩ := d.exists_Delta hp hB hb hbi (d.π_mem i₀ y₀ (hYX hy₀Y))
  have hcY : c ∈ Y := hCY ⟨d.Delta_le_X b i₀ hc, d.Delta_le_cent b i₀ hc⟩
  have hdiv := d.maxl_D_iv hYX hcov hS hi₀ hcY hy₀Y hcπ.symm
  intro j hj
  by_contra hjQ
  have h1 := d.maxl_Delta_van hc hjQ
  have h2 : d.π j y₀ ≠ 1 := (d.maxl_mem_supp y₀ j).1 (hy₀S ▸ hj)
  exact h2 (by rw [← hdiv j hj, h1])

theorem maxl_F (hp : p.Prime) (hB : IsElemAbelian p B) {b : G} (hb : b ∈ B)
    (hmove : ∃ i, d.σ b i ≠ i) {Y : Subgroup G} (hYX : Y ≤ X)
    (hBY : ∀ β ∈ B, ∀ y ∈ Y, β * y * β⁻¹ ∈ Y)
    (hcov : ∀ i, ∀ k ∈ d.K i, ∃ y ∈ Y, d.π i y = k)
    (hK : ∀ i, ∀ y ∈ Y, y ∈ d.K i → y = 1)
    (hCY : X ⊓ Subgroup.centralizer ({b} : Set G) ≤ Y)
    {S : Finset (Fin d.r)} (hS : d.maxl_MinSupp Y S) {i₀ : Fin d.r} (hi₀ : i₀ ∈ S) :
    S = d.maxl_Q b i₀ := by
  have hbi := d.maxl_moves hB hb hmove i₀
  have hE := d.maxl_E hp hB hb hmove hYX hcov hCY hS hi₀
  have hσp := d.maxl_perm_pow_p hB hb
  refine Finset.Subset.antisymm hE ?_
  by_contra hnot
  have hno : ¬ ∀ j, d.σ b j ∈ S ↔ j ∈ S := by
    intro hinv
    apply hnot
    intro j hj
    obtain ⟨m, hm, rfl⟩ := (d.maxl_mem_Q b i₀ j).1 hj
    exact (d.maxl_inv_pow S (d.σ b) hinv m i₀).2 hi₀
  have hdisj : ∀ l, 0 < l → l < p → ∀ j ∈ S, (d.σ b ^ l) j ∉ S := by
    intro l hl0 hlp j hj hjl
    have hinv_l : ∀ j, (d.σ b ^ l) j ∈ S ↔ j ∈ S := by
      have := d.maxl_dichotomy hYX hBY hcov hS (pow_mem hb l)
        ⟨j, hj, by rw [d.σ_pow hb]; exact hjl⟩
      simpa only [d.σ_pow hb] using this
    have hcop : Nat.Coprime p l := (Nat.Prime.coprime_iff_not_dvd hp).2
      (Nat.not_dvd_of_pos_of_lt hl0 hlp)
    obtain ⟨n, -, hn⟩ := Nat.exists_mul_mod_eq_one_of_coprime (n := l) hcop.symm hp.one_lt
    apply hno
    have h2 := d.maxl_inv_pow S (d.σ b ^ l) hinv_l n
    rw [← pow_mul, pow_eq_pow_mod _ hσp, hn, pow_one] at h2
    exact h2
  have hcardQ := d.maxl_card_Q hp hB hb hbi
  have hcnt : (S ×ˢ Finset.range p).card ≤ (d.maxl_Q b i₀).card := by
    refine Finset.card_le_card_of_injOn (fun x : Fin d.r × ℕ => (d.σ b ^ x.2) x.1) ?_ ?_
    · rintro ⟨j, l⟩ hx
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hx
      obtain ⟨hj, hl⟩ := hx
      obtain ⟨m, hm, hmj⟩ := (d.maxl_mem_Q b i₀ j).1 (hE j hj)
      simp only [Finset.mem_coe]
      refine (d.maxl_mem_Q b i₀ _).2 ⟨(l + m) % p, Nat.mod_lt _ hp.pos, ?_⟩
      rw [← pow_eq_pow_mod _ hσp, pow_add, Equiv.Perm.mul_apply, hmj]
    · have key : ∀ l l' : ℕ, l < l' → l' < p → ∀ j ∈ S, ∀ j' ∈ S,
          (d.σ b ^ l) j = (d.σ b ^ l') j' → False := by
        intro l l' hlt hl' j hj j' hj' h
        have e : d.σ b ^ l' = d.σ b ^ l * d.σ b ^ (l' - l) := by
          rw [← pow_add]; congr 1; omega
        have h' : (d.σ b ^ l) j = (d.σ b ^ l) ((d.σ b ^ (l' - l)) j') := by
          rw [e] at h; exact h
        have := (d.σ b ^ l).injective h'
        exact hdisj (l' - l) (by omega) (by omega) j' hj' (this ▸ hj)
      rintro ⟨j, l⟩ hx ⟨j', l'⟩ hx' h
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hx hx'
      simp only at h
      rcases lt_trichotomy l l' with hlt | heq | hgt
      · exact (key l l' hlt hx'.2 j hx.1 j' hx'.1 h).elim
      · subst heq
        have := (d.σ b ^ l).injective h
        rw [this]
      · exact (key l' l hgt hx.2 j' hx'.1 j hx.1 h.symm).elim
  rw [Finset.card_product, Finset.card_range, hcardQ] at hcnt
  have hpos : 0 < S.card := Finset.card_pos.2 ⟨i₀, hi₀⟩
  have hc1 : S.card = 1 := by
    have : S.card * p ≤ 1 * p := by simpa using hcnt
    have := Nat.le_of_mul_le_mul_right this hp.pos
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hc1
  obtain ⟨y₀, hy₀Y, hy₀1, hy₀S⟩ := hS.1
  have hy₀X : y₀ ∈ X := hYX hy₀Y
  have hka : d.π a y₀ ∈ d.K a := d.π_mem a y₀ hy₀X
  have hy₀K : y₀ ∈ d.K a := by
    have : y₀ = d.π a y₀ := by
      refine d.π_ext y₀ hy₀X _ (d.K_le a hka) (fun j => ?_)
      by_cases hja : j = a
      · subst hja; rw [d.π_self j _ hka]
      · rw [d.π_ne j a hja _ hka]
        by_contra hne
        have := (d.maxl_mem_supp y₀ j).2 hne
        rw [hy₀S, ha, Finset.mem_singleton] at this
        exact hja this
    exact this ▸ hka
  exact hy₀1 (hK a y₀ hy₀Y hy₀K)

theorem maxl_G (hp : p.Prime) (hB : IsElemAbelian p B) {b : G} (hb : b ∈ B)
    (hmove : ∃ i, d.σ b i ≠ i) {Y : Subgroup G}
    (hCY : X ⊓ Subgroup.centralizer ({b} : Set G) ≤ Y)
    {S : Finset (Fin d.r)} (hS : d.maxl_MinSupp Y S) {i₀ : Fin d.r}
    (hSQ : S = d.maxl_Q b i₀) (i : Fin d.r) : d.maxl_MinSupp Y (d.maxl_Q b i) := by
  have hbi := d.maxl_moves hB hb hmove i
  have hcardi := d.maxl_card_Q hp hB hb hbi
  have hcard0 := d.maxl_card_Q hp hB hb (d.maxl_moves hB hb hmove i₀)
  refine ⟨?_, fun y hyY hy1 => ?_⟩
  · obtain ⟨a, a', haa⟩ := d.K_nonab i
    have ha1 : a ≠ 1 := fun h => haa (by simp [h])
    have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    obtain ⟨c, hc, hcπ⟩ := d.exists_Delta hp hB hb hbi a.2
    have hcX : c ∈ X := d.Delta_le_X b i hc
    have hcb : b * c * b⁻¹ = c := hc.2.1
    have hc1 : c ≠ 1 := by
      rintro rfl
      rw [d.maxl_π_one] at hcπ
      exact ha1' hcπ.symm
    refine ⟨c, hCY ⟨hcX, d.Delta_le_cent b i hc⟩, hc1, ?_⟩
    ext j
    constructor
    · intro hj
      by_contra hjQ
      exact (d.maxl_mem_supp c j).1 hj (d.maxl_Delta_van hc hjQ)
    · intro hj
      obtain ⟨m, hm, rfl⟩ := (d.maxl_mem_Q b i j).1 hj
      rw [d.maxl_mem_supp, d.coord_pow hb hcX hcb i m, hcπ]
      intro h
      exact ha1' (conj_eq_one_iff.1 h)
  · have := hS.2 y hyY hy1
    rw [hSQ, hcard0] at this
    rwa [hcardi]

theorem maxl_final (hp : p.Prime) (hB : IsElemAbelian p B) {b : G} (hb : b ∈ B)
    (hmove : ∃ i, d.σ b i ≠ i) {Y : Subgroup G} (hYX : Y ≤ X)
    (hcov : ∀ i, ∀ k ∈ d.K i, ∃ y ∈ Y, d.π i y = k)
    (hCY : X ⊓ Subgroup.centralizer ({b} : Set G) ≤ Y)
    (hall : ∀ i, d.maxl_MinSupp Y (d.maxl_Q b i)) :
    ∀ n : ℕ, ∀ y ∈ Y, (d.maxl_supp y).card ≤ n →
      y ∈ X ⊓ Subgroup.centralizer ({b} : Set G) := by
  intro n
  induction n with
  | zero =>
    intro y hyY hcard
    have : y = 1 := by
      by_contra hy1
      obtain ⟨j, hj⟩ := d.maxl_exists_ne_one (hYX hyY) hy1
      have := (d.maxl_mem_supp y j).2 hj
      have h0 : d.maxl_supp y = ∅ := Finset.card_eq_zero.1 (by omega)
      rw [h0] at this
      simp at this
    subst this
    exact one_mem _
  | succ n ih =>
    intro y hyY hcard
    by_cases hy1 : y = 1
    · subst hy1; exact one_mem _
    obtain ⟨i, hi⟩ := d.maxl_exists_ne_one (hYX hyY) hy1
    have hyX : y ∈ X := hYX hyY
    obtain ⟨c, hc, hcπ⟩ := d.exists_Delta hp hB hb (d.maxl_moves hB hb hmove i)
      (d.π_mem i y hyX)
    have hcC : c ∈ X ⊓ Subgroup.centralizer ({b} : Set G) :=
      ⟨d.Delta_le_X b i hc, d.Delta_le_cent b i hc⟩
    have hcY : c ∈ Y := hCY hcC
    have hiQ : i ∈ d.maxl_Q b i := (d.maxl_mem_Q b i i).2 ⟨0, hp.pos, by simp⟩
    have hdiv := d.maxl_D_iv hYX hcov (hall i) hiQ hyY hcY hcπ
    have hy'Y : y * c⁻¹ ∈ Y := mul_mem hyY (inv_mem hcY)
    have hy'π : ∀ j, d.π j (y * c⁻¹) = d.π j y * (d.π j c)⁻¹ :=
      d.maxl_π_mul_inv_X hyX (hYX hcY)
    have hsub : d.maxl_supp (y * c⁻¹) ⊆ (d.maxl_supp y).erase i := by
      intro j hj
      rw [Finset.mem_erase]
      rw [d.maxl_mem_supp, hy'π] at hj
      refine ⟨?_, ?_⟩
      · rintro rfl
        apply hj
        rw [hcπ, mul_inv_cancel]
      · rw [d.maxl_mem_supp]
        intro hjy
        apply hj
        by_cases hjQ : j ∈ d.maxl_Q b i
        · rw [hdiv j hjQ, mul_inv_cancel]
        · rw [hjy, d.maxl_Delta_van hc hjQ]; simp
    have hlt : (d.maxl_supp (y * c⁻¹)).card < (d.maxl_supp y).card := by
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem ((d.maxl_mem_supp y i).2 hi)] at h1
      have : 0 < (d.maxl_supp y).card := Finset.card_pos.2 ⟨i, (d.maxl_mem_supp y i).2 hi⟩
      omega
    have h' := ih (y * c⁻¹) hy'Y (by omega)
    have := mul_mem h' hcC
    simpa using this

theorem maximal (hp : p.Prime) (hB : IsElemAbelian p B) {b : G} (hb : b ∈ B)
    (hmove : ∃ i, d.σ b i ≠ i) {Y : Subgroup G} (hYX : Y ≤ X)
    (hBY : B ≤ Subgroup.normalizer (Y : Set G))
    (hCY : X ⊓ Subgroup.centralizer ({b} : Set G) ≤ Y) :
    Y = X ⊓ Subgroup.centralizer ({b} : Set G) ∨ Y = X := by
  have hBY' : ∀ β ∈ B, ∀ y ∈ Y, β * y * β⁻¹ ∈ Y := fun β hβ y hy => (hBY hβ y).1 hy
  have hcov : ∀ i, ∀ k ∈ d.K i, ∃ y ∈ Y, d.π i y = k := by
    intro i k hk
    obtain ⟨c, hc, hcπ⟩ := d.exists_Delta hp hB hb (d.maxl_moves hB hb hmove i) hk
    exact ⟨c, hCY ⟨d.Delta_le_X b i hc, d.Delta_le_cent b i hc⟩, hcπ⟩
  by_cases hA : ∃ i, d.K i ≤ Y
  ·
    right
    obtain ⟨i, hi⟩ := hA
    refine le_antisymm hYX (d.gen Y (fun j => ?_))
    obtain ⟨β, hβ, hβj⟩ := d.trans i j
    intro k hk
    have hσ : d.σ β⁻¹ j = i := by
      have h1 : d.σ (β⁻¹ * β) = d.σ β⁻¹ * d.σ β := d.σ_mul _ (inv_mem hβ) _ hβ
      rw [inv_mul_cancel, d.σ_one] at h1
      rw [← hβj, ← Equiv.Perm.mul_apply, ← h1]
      rfl
    have hz : β⁻¹ * k * β⁻¹⁻¹ ∈ d.K i := by
      have := d.σ_conj β⁻¹ (inv_mem hβ) j k hk
      rwa [hσ] at this
    have hzY : β⁻¹ * k * β⁻¹⁻¹ ∈ Y := hi hz
    have := hBY' β hβ _ hzY
    have e : β * (β⁻¹ * k * β⁻¹⁻¹) * β⁻¹ = k := by group
    rwa [e] at this
  ·
    left
    push Not at hA
    have hK : ∀ i, ∀ y ∈ Y, y ∈ d.K i → y = 1 := by
      intro i y hyY hyK
      have hnorm : ∀ k ∈ d.K i, ∀ n ∈ Y ⊓ d.K i, k * n * k⁻¹ ∈ Y ⊓ d.K i := by
        intro k hk n hn
        obtain ⟨y', hy'Y, rfl⟩ := hcov i k hk
        have hy'X : y' ∈ X := hYX hy'Y
        have h1 : y' * n * y'⁻¹ ∈ d.K i := d.K_norm i y' hy'X n hn.2
        have h2 : d.π i y' * n * (d.π i y')⁻¹ = y' * n * y'⁻¹ := by
          have := d.maxl_π_conj_X hy'X (hYX hn.1) i
          rw [d.π_self i _ h1, d.π_self i n hn.2] at this
          exact this.symm
        rw [h2]
        exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hy'Y hn.1) (inv_mem hy'Y), h1⟩
      rcases d.maxl_simple_normal i (Y ⊓ d.K i) inf_le_right hnorm with h | h
      · have : y ∈ Y ⊓ d.K i := ⟨hyY, hyK⟩
        rw [h] at this
        exact Subgroup.mem_bot.1 this
      · exact absurd (h.trans inf_le_left) (hA i)
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (d.cent_ne_bot hp hB hb hmove)
    have haY : (a : G) ∈ Y := hCY a.2
    have ha1 : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    obtain ⟨y₀, hy₀mem, hmin⟩ :=
      (measure fun y : G => (d.maxl_supp y).card).wf.has_min {y | y ∈ Y ∧ y ≠ 1} ⟨a, haY, ha1⟩
    have hS : d.maxl_MinSupp Y (d.maxl_supp y₀) :=
      ⟨⟨y₀, hy₀mem.1, hy₀mem.2, rfl⟩, fun y hy hy1 => not_lt.1 (hmin y ⟨hy, hy1⟩)⟩
    obtain ⟨i₀, hi₀⟩ := d.maxl_exists_ne_one (hYX hy₀mem.1) hy₀mem.2
    have hi₀S : i₀ ∈ d.maxl_supp y₀ := (d.maxl_mem_supp y₀ i₀).2 hi₀
    have hSQ := d.maxl_F hp hB hb hmove hYX hBY' hcov hK hCY hS hi₀S
    have hall := d.maxl_G hp hB hb hmove hCY hS hSQ
    refine le_antisymm (fun y hy => ?_) hCY
    exact d.maxl_final hp hB hb hmove hYX hcov hCY hall _ y hy le_rfl
theorem core_comm_of_mem (hB : IsElemAbelian p B) {x y : G} (hx : x ∈ B) (hy : y ∈ B) :
    x * y = y * x := CFSG.Open.IsElemAbelian.comm hB hx hy

theorem core_normalizer_iff (B S : Subgroup G) :
    B ≤ Subgroup.normalizer (S : Set G) ↔ ∀ β ∈ B, ∀ s ∈ S, β * s * β⁻¹ ∈ S := by
  constructor
  · intro h β hβ s hs
    exact (Subgroup.mem_normalizer_iff.1 (h hβ) s).1 hs
  · intro h β hβ
    refine Subgroup.mem_normalizer_iff.2 fun s => ⟨h β hβ s, fun hm => ?_⟩
    have := h β⁻¹ (B.inv_mem hβ) _ hm
    simpa [mul_assoc] using this

theorem core_card_zpowers_le (hB : IsElemAbelian p B) (hp : p.Prime) {x : G} (hx : x ∈ B) :
    Nat.card (Subgroup.zpowers x) ≤ p := by
  rw [Nat.card_zpowers]
  exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hB.2 x hx))

theorem core_exists_not_mem [Finite G] (hp : p.Prime) (hp2 : p ≠ 2)
    (hB2 : p ^ 2 ≤ Nat.card B)
    (T₁ T₂ T₃ : Subgroup G) (h₁ : Nat.card T₁ ≤ p) (h₂ : Nat.card T₂ ≤ p)
    (h₃ : Nat.card T₃ ≤ p) :
    ∃ x ∈ B, x ∉ T₁ ∧ x ∉ T₂ ∧ x ∉ T₃ := by
  by_contra hcon
  push Not at hcon
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have key : ∀ T : Subgroup G, Nat.card T ≤ p → ((T : Set G) \ {1}).ncard + 1 ≤ p := by
    intro T hT
    have h1 : (1 : G) ∈ (T : Set G) := T.one_mem
    rw [Set.ncard_sdiff_singleton_of_mem h1]
    have hpos : 0 < (T : Set G).ncard := by
      rw [Set.ncard_pos]; exact ⟨1, h1⟩
    have : (T : Set G).ncard = Nat.card T := (Nat.card_coe_set_eq _).symm
    omega
  have hsub : (B : Set G) ⊆ (({1} : Set G) ∪ ((T₁ : Set G) \ {1})) ∪ ((T₂ : Set G) \ {1}) ∪
      ((T₃ : Set G) \ {1}) := by
    intro x hx
    by_cases hx1 : x = 1
    · subst hx1; simp
    · by_cases h1 : x ∈ T₁
      · simp [h1, hx1]
      by_cases h2 : x ∈ T₂
      · simp [h2, hx1]
      have h3 := hcon x hx h1 h2
      simp [h3, hx1]
  have hcard : (B : Set G).ncard ≤ 1 + ((T₁ : Set G) \ {1}).ncard + ((T₂ : Set G) \ {1}).ncard +
      ((T₃ : Set G) \ {1}).ncard := by
    calc (B : Set G).ncard ≤ ((({1} : Set G) ∪ ((T₁ : Set G) \ {1})) ∪ ((T₂ : Set G) \ {1}) ∪
          ((T₃ : Set G) \ {1})).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ _ := by
        refine (Set.ncard_union_le _ _).trans ?_
        refine Nat.add_le_add ((Set.ncard_union_le _ _).trans ?_) le_rfl
        refine Nat.add_le_add ((Set.ncard_union_le _ _).trans ?_) le_rfl
        simp
  have hB' : (B : Set G).ncard = Nat.card B := (Nat.card_coe_set_eq _).symm
  have k1 := key T₁ h₁
  have k2 := key T₂ h₂
  have k3 := key T₃ h₃
  nlinarith

theorem core_not_mem_zpowers [Finite G] (hp : p.Prime) (hB : IsElemAbelian p B) {b e : G} (hb : b ∈ B)
    (he : e ∈ B) (hb1 : b ≠ 1) (he1 : e ≠ 1) (hbe : b ∉ Subgroup.zpowers e) :
    e ∉ Subgroup.zpowers b := by
  intro h
  have hle : Subgroup.zpowers e ≤ Subgroup.zpowers b := (Subgroup.zpowers_le).2 h
  have : Fact p.Prime := ⟨hp⟩
  have ob : orderOf b = p := orderOf_eq_prime (hB.2 b hb) hb1
  have oe : orderOf e = p := orderOf_eq_prime (hB.2 e he) he1
  have heq : Subgroup.zpowers e = Subgroup.zpowers b :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, ob, oe])
  exact hbe (heq ▸ Subgroup.mem_zpowers b)

theorem core_cent_inv (hB : IsElemAbelian p B) (hBX : ∀ β ∈ B, ∀ g ∈ X, β * g * β⁻¹ ∈ X)
    {b : G} (hb : b ∈ B) :
    ∀ β ∈ B, ∀ s ∈ X ⊓ Subgroup.centralizer ({b} : Set G), β * s * β⁻¹ ∈
      X ⊓ Subgroup.centralizer ({b} : Set G) := by
  intro β hβ s hs
  refine ⟨hBX β hβ s hs.1, ?_⟩
  have hs2 := Subgroup.mem_centralizer_iff.1 hs.2
  refine Subgroup.mem_centralizer_iff.2 ?_
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have hbs : h * s = s * h := hs2 h rfl
  have hbβ : h * β = β * h := core_comm_of_mem hB hb hβ
  calc h * (β * s * β⁻¹) = β * (h * s) * β⁻¹ := by
        have : β⁻¹ = β⁻¹ := rfl
        calc h * (β * s * β⁻¹) = (h * β) * s * β⁻¹ := by group
          _ = (β * h) * s * β⁻¹ := by rw [hbβ]
          _ = β * (h * s) * β⁻¹ := by group
    _ = β * (s * h) * β⁻¹ := by rw [hbs]
    _ = β * s * β⁻¹ * h := by
        have : h * β⁻¹ = β⁻¹ * h := by
          calc h * β⁻¹ = β⁻¹ * (β * h) * β⁻¹ := by group
            _ = β⁻¹ * (h * β) * β⁻¹ := by rw [hbβ]
            _ = β⁻¹ * h := by group
        calc β * (s * h) * β⁻¹ = β * s * (h * β⁻¹) := by group
          _ = β * s * (β⁻¹ * h) := by rw [this]
          _ = β * s * β⁻¹ * h := by group

theorem core_normalizer_sup (B H K : Subgroup G)
    (hH : ∀ β ∈ B, ∀ s ∈ H, β * s * β⁻¹ ∈ H) (hK : ∀ β ∈ B, ∀ s ∈ K, β * s * β⁻¹ ∈ K) :
    B ≤ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [core_normalizer_iff]
  intro β _ s hs
  have hle : H ⊔ K ≤ (H ⊔ K).comap (MulAut.conj β).toMonoidHom := by
    refine sup_le (fun h hh => ?_) (fun k hk => ?_)
    · exact Subgroup.mem_sup_left (by simpa [MulAut.conj_apply] using hH β ‹_› h hh)
    · exact Subgroup.mem_sup_right (by simpa [MulAut.conj_apply] using hK β ‹_› k hk)
  simpa [MulAut.conj_apply] using hle hs

theorem core_exists_stab (d : FactorData p G B X) (i₀ : Fin d.r) :
    ∃ N : Subgroup G, ∀ β, β ∈ N ↔ β ∈ B ∧ d.σ β i₀ = i₀ := by
  refine ⟨{ carrier := {β | β ∈ B ∧ d.σ β i₀ = i₀}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun β => Iff.rfl⟩
  · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨B.mul_mem ha hb, ?_⟩
    rw [d.σ_mul a ha b hb]
    simp [ha', hb']
  · refine ⟨B.one_mem, ?_⟩
    simp [d.σ_one]
  · rintro a ⟨ha, ha'⟩
    refine ⟨B.inv_mem ha, ?_⟩
    have h1 : d.σ (a⁻¹ * a) = 1 := by
      rw [inv_mul_cancel]; exact d.σ_one
    rw [d.σ_mul a⁻¹ (B.inv_mem ha) a ha] at h1
    have := congrArg (fun f => f i₀) h1
    simpa [ha'] using this

include d in
theorem na_core (hp : p.Prime) (hp2 : p ≠ 2) (hB : IsElemAbelian p B) [Finite G]
    {D : Subgroup G} (hDB : D ≤ B) (hB2 : p ^ 2 ≤ Nat.card B) :
    ⁅X, D⁆ ≤ ⨆ (b : G) (_ : b ∈ B ∧ b ≠ 1), ⁅X ⊓ Subgroup.centralizer ({b} : Set G), D⁆ := by
  by_cases hD : D = ⊥
  · subst hD
    rw [Subgroup.commutator_bot_right]
    exact bot_le
  obtain ⟨e, heD, he1⟩ : ∃ e ∈ D, e ≠ 1 := by
    by_contra h
    push Not at h
    exact hD ((Subgroup.eq_bot_iff_forall D).2 h)
  have heB : e ∈ B := hDB heD
  set R := ⨆ (b : G) (_ : b ∈ B ∧ b ≠ 1), ⁅X ⊓ Subgroup.centralizer ({b} : Set G), D⁆
    with hR
  have hXD : ⁅X, D⁆ ≤ X := by
    rw [Subgroup.commutator_le]
    intro x hx δ hδ
    have h1 : δ * x⁻¹ * δ⁻¹ ∈ X := d.B_norm δ (hDB hδ) x⁻¹ (X.inv_mem hx)
    rw [commutatorElement_def]
    have : x * δ * x⁻¹ * δ⁻¹ = x * (δ * x⁻¹ * δ⁻¹) := by group
    rw [this]
    exact X.mul_mem hx h1
  obtain ⟨N, hN⟩ := core_exists_stab d ⟨0, d.r_pos⟩
  have hNcard : Nat.card N ≤ p := by
    refine d.stab_card ⟨0, d.r_pos⟩ N (fun β hβ => ((hN β).1 hβ).1) ?_
    intro β hβ
    exact ((hN β).1 hβ).2
  have hmoveOf : ∀ b, b ∈ B → b ∉ N → ∃ i, d.σ b i ≠ i := by
    intro b hb hbN
    exact ⟨⟨0, d.r_pos⟩, fun h => hbN ((hN b).2 ⟨hb, h⟩)⟩
  have hone : (1 : G) ∈ N := N.one_mem
  have hecard := core_card_zpowers_le hB hp heB
  obtain ⟨b₁, hb₁B, hb₁N, hb₁e, -⟩ :=
    core_exists_not_mem hp hp2 hB2 N (Subgroup.zpowers e) N hNcard hecard hNcard
  have hb₁c := core_card_zpowers_le hB hp hb₁B
  obtain ⟨b₂, hb₂B, hb₂N, hb₂e, hb₂b₁⟩ :=
    core_exists_not_mem hp hp2 hB2 N (Subgroup.zpowers e) (Subgroup.zpowers b₁) hNcard hecard hb₁c
  have hb₁1 : b₁ ≠ 1 := fun h => hb₁N (h ▸ hone)
  have hb₂1 : b₂ ≠ 1 := fun h => hb₂N (h ▸ hone)
  have hm₁ := hmoveOf b₁ hb₁B hb₁N
  have hm₂ := hmoveOf b₂ hb₂B hb₂N
  have hCR : ∀ b, b ∈ B → b ≠ 1 → (∃ i, d.σ b i ≠ i) → b ∉ Subgroup.zpowers e →
      X ⊓ Subgroup.centralizer ({b} : Set G) ≤ R := by
    intro b hb hb1 hm hbe
    have heb := core_not_mem_zpowers hp hB hb heB hb1 he1 hbe
    have h1 := d.cent_le_comm hp hB hb heB hm heb
    refine h1.trans ?_
    refine (Subgroup.commutator_mono le_rfl ((Subgroup.zpowers_le).2 heD)).trans ?_
    exact le_iSup₂_of_le b ⟨hb, hb1⟩ le_rfl
  have hC₁R := hCR b₁ hb₁B hb₁1 hm₁ hb₁e
  have hC₂R := hCR b₂ hb₂B hb₂1 hm₂ hb₂e
  have hXR : X = X ⊓ Subgroup.centralizer ({b₁} : Set G) ⊔ X ⊓ Subgroup.centralizer ({b₂} : Set G) →
      ⁅X, D⁆ ≤ R := by
    intro h
    refine hXD.trans ?_
    rw [h]
    exact sup_le hC₁R hC₂R
  have hX₁R : X = X ⊓ Subgroup.centralizer ({b₁} : Set G) → ⁅X, D⁆ ≤ R := by
    intro h
    refine hXD.trans ?_
    rw [h]
    exact hC₁R
  have hinv₁ := core_cent_inv hB d.B_norm hb₁B
  have hinv₂ := core_cent_inv hB d.B_norm hb₂B
  have hBn₁ : B ≤ Subgroup.normalizer ((X ⊓ Subgroup.centralizer ({b₁} : Set G) : Subgroup G) :
      Set G) := (core_normalizer_iff B _).2 hinv₁
  have hBY : B ≤ Subgroup.normalizer ((X ⊓ Subgroup.centralizer ({b₁} : Set G) ⊔
      X ⊓ Subgroup.centralizer ({b₂} : Set G) : Subgroup G) : Set G) :=
    core_normalizer_sup B _ _ hinv₁ hinv₂
  have hYX : X ⊓ Subgroup.centralizer ({b₁} : Set G) ⊔ X ⊓ Subgroup.centralizer ({b₂} : Set G)
      ≤ X := sup_le inf_le_left inf_le_left
  rcases d.maximal hp hB hb₁B hm₁ hYX hBY le_sup_left with hY | hY
  · by_cases hXY : X = X ⊓ Subgroup.centralizer ({b₁} : Set G)
    · exact hX₁R hXY
    · have hle : X ⊓ Subgroup.centralizer ({b₂} : Set G) ≤
          X ⊓ Subgroup.centralizer ({b₁} : Set G) := by
        rw [← hY]; exact le_sup_right
      rcases d.maximal hp hB hb₂B hm₂ inf_le_left hBn₁ hle with h2 | h2
      · exfalso
        have hcent : X ⊓ Subgroup.centralizer ({b₁} : Set G) ≤
            Subgroup.centralizer (Subgroup.zpowers b₂ : Set G) := by
          intro c hc
          have hc2 : c ∈ X ⊓ Subgroup.centralizer ({b₂} : Set G) := h2 ▸ hc
          have hcm := Subgroup.mem_centralizer_iff.1 hc2.2 b₂ rfl
          rw [Subgroup.mem_centralizer_iff]
          intro g hg
          obtain ⟨k, rfl⟩ := hg
          exact ((Commute.zpow_right (show Commute c b₂ from hcm.symm) k).symm).eq
        have hbot : ⁅X ⊓ Subgroup.centralizer ({b₁} : Set G), Subgroup.zpowers b₂⁆ = ⊥ :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcent
        have hb₂b₁' : b₂ ∉ Subgroup.zpowers b₁ := hb₂b₁
        have h3 := d.cent_le_comm hp hB hb₁B hb₂B hm₁ hb₂b₁'
        rw [hbot] at h3
        exact d.cent_ne_bot hp hB hb₁B hm₁ (le_bot_iff.1 h3)
      · exact hX₁R h2.symm
  · exact hXR hY.symm

end FactorData

section StructHelpers

open Subgroup

variable {G : Type*} [Group G]

structure struct_Coord {r : ℕ} (X : Subgroup G) (K : Fin r → Subgroup G) where
  E : ((i : Fin r) → K i) ≃* X
  hE : ∀ (i : Fin r) (x : (j : Fin r) → K j), (∀ j, j ≠ i → x j = 1) →
    ((E x : X) : G) = (x i : G)

namespace struct_Coord

variable {r : ℕ} {X : Subgroup G} {K : Fin r → Subgroup G} (c : struct_Coord X K)
include c

theorem coe_mulSingle (i : Fin r) (x : K i) : ((c.E (Pi.mulSingle i x) : X) : G) = x := by
  rw [c.hE i (Pi.mulSingle i x) fun j hj => Pi.mulSingle_eq_of_ne hj _, Pi.mulSingle_eq_same]

theorem K_le (i : Fin r) : K i ≤ X := fun x hx => by
  have := (c.E (Pi.mulSingle i ⟨x, hx⟩)).2
  rwa [c.coe_mulSingle] at this

theorem commute {i j : Fin r} (hij : i ≠ j) {x y : G} (hx : x ∈ K i) (hy : y ∈ K j) :
    x * y = y * x := by
  have h := ((Pi.mulSingle_commute hij (⟨x, hx⟩ : K i) (⟨y, hy⟩ : K j)).map
    c.E.toMonoidHom).map X.subtype
  simp only [Subgroup.subtype_apply, MulEquiv.coe_toMonoidHom, c.coe_mulSingle] at h
  exact h.eq

theorem eq_one_of_mem_of_mem {i j : Fin r} (hij : i ≠ j) {x : G} (hi : x ∈ K i) (hj : x ∈ K j) :
    x = 1 := by
  have h : c.E (Pi.mulSingle i ⟨x, hi⟩) = c.E (Pi.mulSingle j ⟨x, hj⟩) :=
    Subtype.ext (by rw [c.coe_mulSingle, c.coe_mulSingle])
  have h2 := congrFun (c.E.injective h) i
  rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij] at h2
  exact congrArg Subtype.val h2

theorem gen {Y : Subgroup G} (hY : ∀ i, K i ≤ Y) : X ≤ Y := by
  intro m hm
  obtain ⟨x, hx⟩ := c.E.surjective ⟨m, hm⟩
  have hxK : x ∈ Y.comap (X.subtype.comp c.E.toMonoidHom) := by
    refine Subgroup.pi_mem_of_mulSingle_mem x fun i => ?_
    show ((c.E (Pi.mulSingle i (x i)) : X) : G) ∈ Y
    rw [c.coe_mulSingle]
    exact hY i (x i).2
  have h : ((c.E x : X) : G) ∈ Y := hxK
  rwa [hx] at h

theorem K_norm {i : Fin r} {x : G} (hx : x ∈ X) {k : G} (hk : k ∈ K i) : x * k * x⁻¹ ∈ K i := by
  have h : X ≤ Subgroup.normalizer (K i : Set G) := by
    refine c.gen fun j => Subgroup.le_normalizer_iff.mpr fun y hy z hz => ?_
    by_cases hji : j = i
    · subst hji
      exact (K j).mul_mem ((K j).mul_mem hy hz) ((K j).inv_mem hy)
    · rw [c.commute hji hy hz]
      simpa using hz
  exact (h hx k).mp hk

open Classical in
@[expose] noncomputable def pi (i : Fin r) (g : G) : G :=
  if hg : g ∈ X then ((c.E.symm ⟨g, hg⟩ i : K i) : G) else 1

theorem pi_E (x : (j : Fin r) → K j) (i : Fin r) : c.pi i ((c.E x : X) : G) = (x i : G) := by
  have h := (c.E x).2
  simp [pi, h]

theorem exists_E {g : G} (hg : g ∈ X) : ∃ x : (j : Fin r) → K j, ((c.E x : X) : G) = g :=
  ⟨c.E.symm ⟨g, hg⟩, by simp⟩

theorem pi_mem (i : Fin r) {g : G} (hg : g ∈ X) : c.pi i g ∈ K i := by
  obtain ⟨x, rfl⟩ := c.exists_E hg
  rw [c.pi_E]
  exact (x i).2

theorem pi_mul (i : Fin r) {g h : G} (hg : g ∈ X) (hh : h ∈ X) :
    c.pi i (g * h) = c.pi i g * c.pi i h := by
  obtain ⟨x, rfl⟩ := c.exists_E hg
  obtain ⟨y, rfl⟩ := c.exists_E hh
  have : ((c.E x : X) : G) * ((c.E y : X) : G) = ((c.E (x * y) : X) : G) := by
    rw [map_mul]; rfl
  rw [this, c.pi_E, c.pi_E, c.pi_E]
  rfl

theorem pi_self (i : Fin r) {k : G} (hk : k ∈ K i) : c.pi i k = k := by
  have := c.pi_E (Pi.mulSingle i ⟨k, hk⟩) i
  rwa [c.coe_mulSingle, Pi.mulSingle_eq_same] at this

theorem pi_ne {i j : Fin r} (hij : i ≠ j) {k : G} (hk : k ∈ K j) : c.pi i k = 1 := by
  have := c.pi_E (Pi.mulSingle j ⟨k, hk⟩) i
  rw [c.coe_mulSingle, Pi.mulSingle_eq_of_ne hij] at this
  simpa using this

theorem pi_ext {g h : G} (hg : g ∈ X) (hh : h ∈ X) (H : ∀ i, c.pi i g = c.pi i h) : g = h := by
  obtain ⟨x, rfl⟩ := c.exists_E hg
  obtain ⟨y, rfl⟩ := c.exists_E hh
  have : x = y := by
    funext i
    exact Subtype.ext (by simpa only [c.pi_E] using H i)
  rw [this]

theorem exists_of_coord (f : Fin r → G) (hf : ∀ i, f i ∈ K i) :
    ∃ g ∈ X, ∀ i, c.pi i g = f i :=
  ⟨((c.E fun i => ⟨f i, hf i⟩ : X) : G), (c.E _).2, fun i => by rw [c.pi_E]⟩

end struct_Coord

theorem struct_center_trivial {K : Type*} [Group K] [IsSimpleGroup K]
    (hn : ∃ a b : K, a * b ≠ b * a) {z : K} (h : ∀ k : K, z * k = k * z) : z = 1 := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center K) with h0 | h0
  · have : z ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr (fun k => (h k).symm)
    rw [h0] at this
    exact Subgroup.mem_bot.mp this
  · exfalso
    obtain ⟨a, b, hab⟩ := hn
    have : a ∈ Subgroup.center K := h0 ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp this b).symm

namespace struct_Coord

variable {r : ℕ} {X : Subgroup G} {K : Fin r → Subgroup G} (c : struct_Coord X K)
include c

theorem pi_one (i : Fin r) : c.pi i 1 = 1 := c.pi_self i (K i).one_mem

theorem X_center (hs : ∀ i, IsSimpleGroup (K i)) (hn : ∀ i, ∃ a b : K i, a * b ≠ b * a)
    {z : G} (hz : z ∈ X) (h : ∀ x ∈ X, z * x = x * z) : z = 1 := by
  refine c.pi_ext hz X.one_mem fun i => ?_
  rw [c.pi_one]
  have := hs i
  have h1 : (⟨c.pi i z, c.pi_mem i hz⟩ : K i) = 1 := by
    refine struct_center_trivial (hn i) fun k => ?_
    apply Subtype.ext
    have h2 := c.pi_mul i hz (c.K_le i k.2)
    have h3 := c.pi_mul i (c.K_le i k.2) hz
    rw [h (k : G) (c.K_le i k.2), h3, c.pi_self i k.2] at h2
    simpa [c.pi_self i k.2] using h2.symm
  exact congrArg Subtype.val h1

theorem exists_eq_of_simple (hs : ∀ i, IsSimpleGroup (K i))
    (hn : ∀ i, ∃ a b : K i, a * b ≠ b * a)
    {N : Subgroup G} (hNX : N ≤ X) (hNn : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hNs : IsSimpleGroup N) : ∃ k, N = K k := by
  by_contra h
  push Not at h
  have hdisj : ∀ k, N ⊓ K k = ⊥ := by
    intro k
    rcases (Subgroup.isSimpleGroup_iff.mp (hs k)).2 (N ⊓ K k) inf_le_right
        ((Subgroup.normal_subgroupOf_iff inf_le_right).mpr fun x s hx hs' =>
          Subgroup.mem_inf.mpr ⟨hNn s (c.K_le k hs') x (Subgroup.mem_inf.mp hx).1,
            (K k).mul_mem ((K k).mul_mem hs' (Subgroup.mem_inf.mp hx).2) ((K k).inv_mem hs')⟩)
      with h1 | h1
    · exact h1
    · exfalso
      have hle : K k ≤ N := inf_eq_right.mp h1
      rcases (Subgroup.isSimpleGroup_iff.mp hNs).2 (K k) hle
          ((Subgroup.normal_subgroupOf_iff hle).mpr fun x n hx hn' => c.K_norm (hNX hn') hx)
        with h2 | h2
      · exact (Subgroup.isSimpleGroup_iff.mp (hs k)).1 h2
      · exact h k h2.symm
  have hcomm : ∀ k, K k ≤ Subgroup.centralizer (N : Set G) := by
    intro k s hs'
    rw [Subgroup.mem_centralizer_iff]
    intro n hn'
    have h1 : n * s * n⁻¹ * s⁻¹ ∈ N ⊓ K k := by
      refine Subgroup.mem_inf.mpr ⟨?_, (K k).mul_mem (c.K_norm (hNX hn') hs') ((K k).inv_mem hs')⟩
      have := N.mul_mem hn' (hNn s (c.K_le k hs') n⁻¹ (N.inv_mem hn'))
      simpa only [mul_assoc] using this
    rw [hdisj k, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have hN : N ≤ Subgroup.centralizer (X : Set G) :=
    Subgroup.le_centralizer_iff.mpr (c.gen hcomm)
  refine (Subgroup.isSimpleGroup_iff.mp hNs).1 (eq_bot_iff.mpr fun n hn' => ?_)
  rw [Subgroup.mem_bot]
  exact c.X_center hs hn (hNX hn') fun x hx => ((Subgroup.mem_centralizer_iff.mp (hN hn')) x hx).symm

theorem K_injective (hs : ∀ i, IsSimpleGroup (K i)) {i j : Fin r} (h : K i = K j) : i = j := by
  by_contra hij
  have hne := (Subgroup.isSimpleGroup_iff.mp (hs i)).1
  apply hne
  rw [eq_bot_iff]
  intro x hx
  exact Subgroup.mem_bot.mpr (c.eq_one_of_mem_of_mem hij hx (h ▸ hx))

end struct_Coord

theorem struct_nonab {r : ℕ} {X : Subgroup G} {K : Fin r → Subgroup G} (c : struct_Coord X K)
    (hns : ¬ Group.IsSolvable ↥X) (hconj : ∀ i j, ∃ g : G, ∀ x ∈ K j, g * x * g⁻¹ ∈ K i) :
    ∀ i, ∃ a b : K i, a * b ≠ b * a := by
  intro i
  by_contra hcon
  push Not at hcon
  apply hns
  refine Group.isSolvable_of_comm fun x y => ?_
  refine Subtype.ext (c.pi_ext (X.mul_mem x.2 y.2) (X.mul_mem y.2 x.2) fun l => ?_)
  simp only [Subgroup.coe_mul]
  rw [c.pi_mul l x.2 y.2, c.pi_mul l y.2 x.2]
  obtain ⟨g, hg⟩ := hconj i l
  have ha := hg _ (c.pi_mem l x.2)
  have hb := hg _ (c.pi_mem l y.2)
  have h := hcon ⟨_, ha⟩ ⟨_, hb⟩
  have h' := congrArg Subtype.val h
  simp only [Subgroup.coe_mul] at h'
  have e1 : g * (c.pi l x * c.pi l y) * g⁻¹ = g * c.pi l x * g⁻¹ * (g * c.pi l y * g⁻¹) := by group
  have e2 : g * (c.pi l y * c.pi l x) * g⁻¹ = g * c.pi l y * g⁻¹ * (g * c.pi l x * g⁻¹) := by group
  have h3 : g * (c.pi l x * c.pi l y) * g⁻¹ = g * (c.pi l y * c.pi l x) * g⁻¹ := by
    rw [e1, e2]; exact h'
  simpa using h3

theorem struct_catalog {X : Subgroup G} (hXK : IsKGroup ↥X) {K : Subgroup G} (hKX : K ≤ X)
    (hs : IsSimpleGroup K) (hn : ∃ a b : K, a * b ≠ b * a) : IsCatalogGroup ↥K := by
  let K' : Subgroup X := K.subgroupOf X
  let e1 : K' ≃* K := Subgroup.subgroupOfEquivOfLe hKX
  let e2 : K' ⧸ (⊥ : Subgroup X).subgroupOf K' ≃* K' :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf (H := K'))).trans
      QuotientGroup.quotientBot
  let e : K' ⧸ (⊥ : Subgroup X).subgroupOf K' ≃* K := e2.trans e1
  have : ((⊥ : Subgroup X).subgroupOf K').Normal := inferInstance
  have hsq : IsSimpleGroup (K' ⧸ (⊥ : Subgroup X).subgroupOf K') := e.isSimpleGroup
  have hnq : ∃ a b : K' ⧸ (⊥ : Subgroup X).subgroupOf K', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hn
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  obtain ⟨i, ⟨φ⟩⟩ := hXK K' ⊥ bot_le hsq hnq
  exact ⟨i, ⟨e.symm.trans φ⟩⟩

@[expose] def struct_conjAut (K : Subgroup G) (s : G) (h1 : ∀ k ∈ K, s * k * s⁻¹ ∈ K)
    (h2 : ∀ k ∈ K, s⁻¹ * k * s ∈ K) : MulAut ↥K where
  toFun k := ⟨s * k * s⁻¹, h1 k k.2⟩
  invFun k := ⟨s⁻¹ * k * s, h2 k k.2⟩
  left_inv k := Subtype.ext (by simp [mul_assoc])
  right_inv k := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

structure struct_Setup {r : ℕ} (B X : Subgroup G) (K : Fin r → Subgroup G) extends
    struct_Coord X K where
  simple : ∀ i, IsSimpleGroup (K i)
  nonab : ∀ i, ∃ a b : K i, a * b ≠ b * a
  B_norm : ∀ β ∈ B, ∀ g ∈ X, β * g * β⁻¹ ∈ X

namespace struct_Setup

variable {r : ℕ} {B X : Subgroup G} {K : Fin r → Subgroup G} (d : struct_Setup B X K)
include d

theorem X_induction {P : G → Prop} (h1 : P 1) (hmul : ∀ g h, g ∈ X → h ∈ X → P g → P h → P (g * h))
    (hinv : ∀ g, g ∈ X → P g → P g⁻¹) (hK : ∀ i, ∀ k ∈ K i, P k) : ∀ g ∈ X, P g := by
  let Y : Subgroup G :=
    { carrier := {g | g ∈ X ∧ P g}
      mul_mem' := fun {a b} ha hb => ⟨X.mul_mem ha.1 hb.1, hmul a b ha.1 hb.1 ha.2 hb.2⟩
      one_mem' := ⟨X.one_mem, h1⟩
      inv_mem' := fun {a} ha => ⟨X.inv_mem ha.1, hinv a ha.1 ha.2⟩ }
  have hY : X ≤ Y := d.gen fun i k hk => ⟨d.K_le i hk, hK i k hk⟩
  exact fun g hg => (hY hg).2

theorem exists_conj_index {β : G} (hβ : β ∈ B) (i : Fin r) :
    ∃ j, ∀ y, y ∈ K j ↔ β⁻¹ * y * β ∈ K i := by
  have := d.simple i
  have hN : IsSimpleGroup ((K i).map (MulAut.conj β).toMonoidHom) :=
    MulEquiv.isSimpleGroup ((K i).equivMapOfInjective _ (MulAut.conj β).injective).symm
  obtain ⟨j, hj⟩ := d.exists_eq_of_simple d.simple d.nonab (N := (K i).map (MulAut.conj β).toMonoidHom)
    (by
      rintro _ ⟨k, hk, rfl⟩
      exact d.B_norm β hβ k (d.K_le i hk))
    (by
      rintro x hx _ ⟨k, hk, rfl⟩
      refine ⟨(β⁻¹ * x * β) * k * (β⁻¹ * x * β)⁻¹, d.K_norm ?_ hk, ?_⟩
      · simpa using d.B_norm β⁻¹ (B.inv_mem hβ) x hx
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group)
    hN
  refine ⟨j, fun y => ?_⟩
  rw [← hj]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hk
  · intro hy
    exact ⟨_, hy, by simp [mul_assoc]⟩

open Classical in
@[expose] noncomputable def sigmaIdx (β : G) (i : Fin r) : Fin r :=
  if h : β ∈ B then Classical.choose (d.exists_conj_index h i) else i

theorem sigmaIdx_spec {β : G} (hβ : β ∈ B) (i : Fin r) (y : G) :
    y ∈ K (d.sigmaIdx β i) ↔ β⁻¹ * y * β ∈ K i := by
  have h := Classical.choose_spec (d.exists_conj_index hβ i) y
  simpa [sigmaIdx, hβ] using h

theorem sigmaIdx_unique {β : G} (hβ : β ∈ B) {i j : Fin r} (h : ∀ k ∈ K i, β * k * β⁻¹ ∈ K j) :
    d.sigmaIdx β i = j := by
  have := d.simple i
  obtain ⟨k, hk⟩ := exists_ne (1 : K i)
  by_contra hne
  have h1 : β * (k : G) * β⁻¹ ∈ K (d.sigmaIdx β i) :=
    (d.sigmaIdx_spec hβ i _).mpr (by simp [mul_assoc])
  have h2 := d.eq_one_of_mem_of_mem hne h1 (h k k.2)
  apply hk
  apply Subtype.ext
  have h3 : (k : G) = β⁻¹ * (β * (k : G) * β⁻¹) * β := by group
  rw [h2] at h3
  simpa using h3

theorem sigmaIdx_injective {β : G} (hβ : β ∈ B) : Function.Injective (d.sigmaIdx β) := by
  intro i i' h
  refine d.K_injective d.simple ?_
  ext y
  have h1 := d.sigmaIdx_spec hβ i (β * y * β⁻¹)
  have h2 := d.sigmaIdx_spec hβ i' (β * y * β⁻¹)
  rw [h] at h1
  have e : β⁻¹ * (β * y * β⁻¹) * β = y := by group
  rw [e] at h1 h2
  exact h1.symm.trans h2

open Classical in
@[expose] noncomputable def sigma (β : G) : Equiv.Perm (Fin r) :=
  if hβ : β ∈ B then
    Equiv.ofBijective (d.sigmaIdx β) (Finite.injective_iff_bijective.mp (d.sigmaIdx_injective hβ))
  else 1

theorem sigma_apply {β : G} (hβ : β ∈ B) (i : Fin r) : d.sigma β i = d.sigmaIdx β i := by
  simp [sigma, hβ]

theorem sigma_unique {β : G} (hβ : β ∈ B) {i j : Fin r} (h : ∀ k ∈ K i, β * k * β⁻¹ ∈ K j) :
    d.sigma β i = j := by
  rw [d.sigma_apply hβ]
  exact d.sigmaIdx_unique hβ h

theorem sigma_iff {β : G} (hβ : β ∈ B) (i : Fin r) (y : G) :
    y ∈ K (d.sigma β i) ↔ β⁻¹ * y * β ∈ K i := by
  rw [d.sigma_apply hβ]
  exact d.sigmaIdx_spec hβ i y

theorem sigma_conj {β : G} (hβ : β ∈ B) (i : Fin r) {k : G} (hk : k ∈ K i) :
    β * k * β⁻¹ ∈ K (d.sigma β i) :=
  (d.sigma_iff hβ i _).mpr (by simpa [mul_assoc] using hk)

theorem sigma_mul {β γ : G} (hβ : β ∈ B) (hγ : γ ∈ B) :
    d.sigma (β * γ) = d.sigma β * d.sigma γ := by
  refine Equiv.ext fun i => ?_
  rw [Equiv.Perm.mul_apply]
  refine d.sigma_unique (B.mul_mem hβ hγ) fun k hk => ?_
  have := d.sigma_conj hβ _ (d.sigma_conj hγ i hk)
  simpa [mul_assoc] using this

theorem sigma_one : d.sigma 1 = 1 := by
  refine Equiv.ext fun i => ?_
  exact d.sigma_unique B.one_mem fun k hk => by simpa using hk

theorem pi_inv (i : Fin r) {g : G} (hg : g ∈ X) : d.pi i g⁻¹ = (d.pi i g)⁻¹ := by
  have h := d.pi_mul i hg (X.inv_mem hg)
  rw [mul_inv_cancel, d.pi_one] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem pi_conj {β : G} (hβ : β ∈ B) {g : G} (hg : g ∈ X) (i : Fin r) :
    d.pi (d.sigma β i) (β * g * β⁻¹) = β * d.pi i g * β⁻¹ := by
  revert i
  refine d.X_induction (P := fun g => ∀ i, d.pi (d.sigma β i) (β * g * β⁻¹) = β * d.pi i g * β⁻¹)
    ?_ ?_ ?_ ?_ g hg
  · intro i
    simp [d.pi_one]
  · intro g h hg hh Pg Ph i
    have e : β * (g * h) * β⁻¹ = (β * g * β⁻¹) * (β * h * β⁻¹) := by group
    rw [e, d.pi_mul _ (d.B_norm β hβ g hg) (d.B_norm β hβ h hh), Pg, Ph, d.pi_mul _ hg hh]
    group
  · intro g hg Pg i
    have e : β * g⁻¹ * β⁻¹ = (β * g * β⁻¹)⁻¹ := by group
    rw [e, d.pi_inv _ (d.B_norm β hβ g hg), Pg, d.pi_inv _ hg]
    group
  · intro l k hk i
    have hk' := d.sigma_conj hβ l hk
    by_cases hil : i = l
    · subst hil
      rw [d.pi_self _ hk', d.pi_self _ hk]
    · have hne : d.sigma β i ≠ d.sigma β l := fun h => hil ((d.sigma β).injective h)
      rw [d.pi_ne hne hk', d.pi_ne hil hk]
      group

theorem faithful {β : G} (hβ : β ∈ B) (hfaith : B ⊓ Subgroup.centralizer (X : Set G) = ⊥)
    (h : ∀ i, ∀ k ∈ K i, β * k * β⁻¹ = k) : β = 1 := by
  have hX := d.X_induction (P := fun g => β * g * β⁻¹ = g) (by simp)
    (fun g h hg hh Pg Ph => by
      have e : β * (g * h) * β⁻¹ = (β * g * β⁻¹) * (β * h * β⁻¹) := by group
      rw [e, Pg, Ph])
    (fun g hg Pg => by
      have e : β * g⁻¹ * β⁻¹ = (β * g * β⁻¹)⁻¹ := by group
      rw [e, Pg]) h
  have hmem : β ∈ B ⊓ Subgroup.centralizer (X : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨hβ, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have := hX x hx
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  rw [hfaith] at hmem
  exact Subgroup.mem_bot.mp hmem

@[expose] def transSub : Subgroup G where
  carrier := {g | ∃ β ∈ B, ∀ i, ∀ y, y ∈ K i ↔ g * y * g⁻¹ ∈ K (d.sigma β i)}
  mul_mem' := by
    rintro a b ⟨β, hβ, ha⟩ ⟨γ, hγ, hb⟩
    refine ⟨β * γ, B.mul_mem hβ hγ, fun i y => ?_⟩
    rw [d.sigma_mul hβ hγ, Equiv.Perm.mul_apply, hb i y, ha (d.sigma γ i)]
    have e : a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
    rw [e]
  one_mem' := ⟨1, B.one_mem, fun i y => by simp [d.sigma_one]⟩
  inv_mem' := by
    rintro a ⟨β, hβ, ha⟩
    refine ⟨β⁻¹, B.inv_mem hβ, fun i y => ?_⟩
    have h := ha (d.sigma β⁻¹ i) (a⁻¹ * y * a)
    have e : a * (a⁻¹ * y * a) * a⁻¹ = y := by group
    rw [e] at h
    have e2 : d.sigma β (d.sigma β⁻¹ i) = i := by
      rw [← Equiv.Perm.mul_apply, ← d.sigma_mul hβ (B.inv_mem hβ), mul_inv_cancel, d.sigma_one]
      rfl
    rw [e2] at h
    rw [inv_inv]
    exact h.symm

theorem mem_transSub {g : G} : g ∈ d.transSub ↔
    ∃ β ∈ B, ∀ i, ∀ y, y ∈ K i ↔ g * y * g⁻¹ ∈ K (d.sigma β i) := Iff.rfl

theorem sup_le_transSub : X ⊔ B ≤ d.transSub := by
  refine sup_le (fun g hg => ?_) (fun β hβ => ?_)
  · refine ⟨1, B.one_mem, fun i y => ?_⟩
    rw [d.sigma_one]
    change _ ↔ _ ∈ K i
    exact ⟨fun hy => d.K_norm hg hy, fun hy => by simpa [mul_assoc] using d.K_norm (X.inv_mem hg) hy⟩
  · refine ⟨β, hβ, fun i y => ?_⟩
    have e : β⁻¹ * (β * y * β⁻¹) * β = y := by group
    rw [d.sigma_iff hβ i (β * y * β⁻¹), e]

theorem trans (hconj : ∀ i j, ∃ g ∈ X ⊔ B, ∀ x, x ∈ K j ↔ g * x * g⁻¹ ∈ K i) :
    ∀ i j, ∃ β ∈ B, d.sigma β i = j := by
  intro i j
  obtain ⟨g, hg, hx⟩ := hconj j i
  obtain ⟨β, hβ, hgβ⟩ := d.sup_le_transSub hg
  refine ⟨β, hβ, ?_⟩
  refine d.K_injective d.simple ?_
  ext z
  have h1 := hx (g⁻¹ * z * g)
  have h2 := hgβ i (g⁻¹ * z * g)
  have e : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
  rw [e] at h1 h2
  exact h2.symm.trans h1

end struct_Setup

end StructHelpers

section StructStab

theorem struct_stab_card {G : Type} [Group G] [Finite G] {r : ℕ} {B X : Subgroup G}
    {K : Fin r → Subgroup G} (d : struct_Setup B X K) (h713 : I_7_13_1_pPrime) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hB : IsElemAbelian p B) (hX : ¬ p ∣ Nat.card X)
    (hXK : IsKGroup ↥X) (hfaith : B ⊓ Subgroup.centralizer (X : Set G) = ⊥)
    (htrans : ∀ i j, ∃ β ∈ B, d.sigma β i = j) (i : Fin r) (S : Subgroup G) (hSB : S ≤ B)
    (hS : ∀ β ∈ S, d.sigma β i = i) : Nat.card S ≤ p := by
  have hsimple := d.simple i
  have hcat : IsCatalogGroup ↥(K i) := struct_catalog hXK (d.K_le i) hsimple (d.nonab i)
  have hnd : ¬ p ∣ Nat.card (K i) := fun h =>
    hX (h.trans (Subgroup.card_dvd_of_le (d.K_le i)))
  have h1 : ∀ s : S, ∀ k ∈ K i, (s : G) * k * (s : G)⁻¹ ∈ K i := fun s k hk => by
    have := d.sigma_conj (hSB s.2) i hk
    rwa [hS s s.2] at this
  have h2 : ∀ s : S, ∀ k ∈ K i, (s : G)⁻¹ * k * (s : G) ∈ K i := fun s k hk => by
    have := d.sigma_conj (hSB (S.inv_mem s.2)) i hk
    rwa [hS _ (S.inv_mem s.2), inv_inv] at this
  let f : S →* MulAut ↥(K i) :=
    MonoidHom.mk' (fun s => struct_conjAut (K i) s (h1 s) (h2 s)) fun a b =>
      MulEquiv.ext fun k => Subtype.ext (by simp [struct_conjAut, mul_assoc])
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro s hs1
    have hfix : ∀ k ∈ K i, (s : G) * k * (s : G)⁻¹ = k := fun k hk => by
      have := congrArg (fun φ : MulAut ↥(K i) => ((φ ⟨k, hk⟩ : K i) : G)) hs1
      simpa [f, struct_conjAut] using this
    refine Subtype.ext (d.faithful (hSB s.2) hfaith fun j k hk => ?_)
    obtain ⟨β, hβ, hβj⟩ := htrans i j
    subst hβj
    have hk' : (β⁻¹ * k * β) ∈ K i := (d.sigma_iff hβ i k).mp hk
    have hcomm : (s : G) * β = β * s := hB.1.is_comm.comm (⟨s, hSB s.2⟩ : B) ⟨β, hβ⟩ |> congrArg Subtype.val
    have e : k = β * (β⁻¹ * k * β) * β⁻¹ := by group
    have := hfix _ hk'
    generalize (s : G) = t at hcomm hfix this ⊢
    calc t * k * t⁻¹ = (t * β) * (β⁻¹ * k * β) * (t * β)⁻¹ * (β * β⁻¹) := by group
      _ = (β * t) * (β⁻¹ * k * β) * (β * t)⁻¹ * (β * β⁻¹) := by rw [hcomm]
      _ = β * (t * (β⁻¹ * k * β) * t⁻¹) * β⁻¹ := by group
      _ = k := by rw [this]; exact e.symm
  have : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p S := fun x => ⟨1, by
    have := hB.2 x (hSB x.2)
    apply Subtype.ext
    simpa using this⟩
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  have hcomm : ∀ a b : S, a * b = b * a := fun a b => by
    apply Subtype.ext
    have := congrArg Subtype.val (hB.1.is_comm.comm (⟨a, hSB a.2⟩ : B) ⟨b, hSB b.2⟩)
    exact this
  have hpow : ∀ a : S, a ^ p = 1 := fun a => by
    apply Subtype.ext
    simpa using hB.2 a (hSB a.2)
  have hle := CFSG.SectionRank.le_pRank_of_injective hp.one_lt hcomm hpow hk f hf
    (H := (⊤ : Subgroup (MulAut ↥(K i)))) le_top
  have hrk := h713 p hp hp2 ↥(K i) hsimple (d.nonab i) hcat hnd
  have hk1 : k ≤ 1 := hle.trans hrk
  rw [hk]
  calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
    _ = p := pow_one p

end StructStab

theorem exists_factorData (h713 : I_7_13_1_pPrime) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G : Type} [Group G] [Finite G] {B X : Subgroup G}
    (hB : IsElemAbelian p B) (hBX : B ≤ Subgroup.normalizer (X : Set G))
    (hX : ¬ p ∣ Nat.card X) (hXK : IsKGroup ↥X)
    (hfaith : B ⊓ Subgroup.centralizer (X : Set G) = ⊥)
    (hX1 : X ≠ ⊥) (hns : ¬ Group.IsSolvable ↥X)
    (hmin : ∀ M : Subgroup G, M ≤ X → X ≤ Subgroup.normalizer (M : Set G) →
      B ≤ Subgroup.normalizer (M : Set G) → M = ⊥ ∨ M = X) :
    Nonempty (FactorData p G B X) := by
  classical
  obtain ⟨H, hH⟩ : ∃ H : Subgroup G, H = X ⊔ B := ⟨_, rfl⟩
  have hXH : X ≤ H := hH ▸ le_sup_left
  have hBH : B ≤ H := hH ▸ le_sup_right
  have hHn : H ≤ Subgroup.normalizer (X : Set G) :=
    hH ▸ sup_le Subgroup.le_normalizer hBX
  have hNn : (X.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff hXH).mpr fun x g hx hg => ((hHn hg) x).mp hx
  have hN1 : X.subgroupOf H ≠ ⊥ := fun h => hX1 (eq_bot_iff.mpr fun x hx => by
    have h1 : (⟨x, hXH hx⟩ : H) ∈ X.subgroupOf H := hx
    rw [h] at h1
    exact congrArg Subtype.val (Subgroup.mem_bot.mp h1))
  have hNmin : ∀ M : Subgroup H, M.Normal → M ≤ X.subgroupOf H →
      M = ⊥ ∨ M = X.subgroupOf H := by
    intro M hM hMN
    have key : ∀ g ∈ H, ∀ k ∈ M.map H.subtype, g * k * g⁻¹ ∈ M.map H.subtype := by
      rintro g hg _ ⟨m, hm, rfl⟩
      exact ⟨⟨g, hg⟩ * m * ⟨g, hg⟩⁻¹, hM.conj_mem m hm _, by simp⟩
    have hM'X : M.map H.subtype ≤ X := by
      rintro _ ⟨m, hm, rfl⟩
      exact hMN hm
    rcases hmin (M.map H.subtype) hM'X (Subgroup.le_normalizer_iff.mpr fun x hx => key x (hXH hx))
      (Subgroup.le_normalizer_iff.mpr fun b hb => key b (hBH hb)) with h | h
    · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp h)
    · refine Or.inr (Subgroup.map_injective H.subtype_injective ?_)
      rw [h, Subgroup.map_subgroupOf_eq_of_le hXH]
  obtain ⟨r, S, hr, hSN, hSsimple, hSconj, hSnormal, e, he⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hNn hN1 hNmin
  let K : Fin r → Subgroup G := fun i => (S i).map H.subtype
  let eK : ∀ i, S i ≃* K i := fun i => (S i).equivMapOfInjective H.subtype H.subtype_injective
  have eK_coe : ∀ i (y : S i), ((eK i y : K i) : G) = ((y : H) : G) := fun i y => rfl
  let E : ((i : Fin r) → K i) ≃* X :=
    (MulEquiv.piCongrRight fun i => (eK i).symm).trans
      (e.trans (Subgroup.subgroupOfEquivOfLe hXH))
  have hE : ∀ (i : Fin r) (x : (j : Fin r) → K j), (∀ j, j ≠ i → x j = 1) →
      ((E x : X) : G) = (x i : G) := by
    intro i x hx
    have h1 := he i ((MulEquiv.piCongrRight fun i => (eK i).symm) x) (fun j hj => by
      simp [hx j hj])
    have h2 : ((E x : X) : G) = (((e ((MulEquiv.piCongrRight fun i => (eK i).symm) x) :
        X.subgroupOf H) : H) : G) := rfl
    rw [h2, h1]
    exact congrArg Subtype.val ((eK i).apply_symm_apply (x i))
  let c : struct_Coord X K := ⟨E, hE⟩
  have hKsimple : ∀ i, IsSimpleGroup ↥(K i) := fun i => by
    have := hSsimple i
    exact (eK i).symm.isSimpleGroup
  have hconj : ∀ i j, ∃ g ∈ X ⊔ B, ∀ x, x ∈ K j ↔ g * x * g⁻¹ ∈ K i := by
    intro i j
    obtain ⟨g, hg⟩ := hSconj i j
    have hmem : ∀ y : H, y ∈ S j ↔ g * y * g⁻¹ ∈ S i := by
      intro y
      rw [hg]
      constructor
      · rintro ⟨s, hs, rfl⟩
        simpa [CFSG.conjugate, mul_assoc] using hs
      · intro hy
        exact ⟨_, hy, by simp [mul_assoc]⟩
    refine ⟨(g : G), hH ▸ g.2, fun x => ?_⟩
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨g * y * g⁻¹, (hmem y).mp hy, by simp⟩
    · rintro ⟨z, hz, hzx⟩
      refine ⟨g⁻¹ * z * g, (hmem _).mpr (by simpa [mul_assoc] using hz), ?_⟩
      have : ((g⁻¹ * z * g : H) : G) = (g : G)⁻¹ * (z : G) * (g : G) := by simp
      have hz2 : (z : G) = (g : G) * x * (g : G)⁻¹ := hzx
      rw [Subgroup.subtype_apply, this, hz2]
      group
  have hconj' : ∀ i j, ∃ g : G, ∀ x ∈ K j, g * x * g⁻¹ ∈ K i := fun i j => by
    obtain ⟨g, -, hg⟩ := hconj i j
    exact ⟨g, fun x hx => (hg x).mp hx⟩
  let d : struct_Setup B X K :=
    { c with
      simple := hKsimple
      nonab := struct_nonab c hns hconj'
      B_norm := fun β hβ g hg => ((hBX hβ) g).mp hg }
  have htrans := d.trans hconj
  exact ⟨{
    r := r
    r_pos := hr
    K := K
    π := d.pi
    σ := d.sigma
    K_le := d.K_le
    K_simple := hKsimple
    K_nonab := d.nonab
    K_norm := fun i x hx k hk => d.K_norm hx hk
    K_comm := fun i j hij x hx y hy => d.commute hij hx hy
    π_mem := fun i g hg => d.pi_mem i hg
    π_mul := fun i g hg h hh => d.pi_mul i hg hh
    π_self := fun i k hk => d.pi_self i hk
    π_ne := fun i j hij k hk => d.pi_ne hij hk
    π_ext := fun g hg h hh H => d.pi_ext hg hh H
    exists_of_coord := d.exists_of_coord
    gen := fun Y hY => d.gen hY
    B_norm := d.B_norm
    σ_mul := fun β hβ γ hγ => d.sigma_mul hβ hγ
    σ_conj := fun β hβ i k hk => d.sigma_conj hβ i hk
    π_conj := fun β hβ g hg i => d.pi_conj hβ hg i
    trans := htrans
    faithful := fun β hβ h => d.faithful hβ hfaith h
    stab_card := fun i S hSB hS =>
      struct_stab_card d h713 hp hp2 hB hX hXK hfaith htrans i S hSB hS }⟩

end NonabelianCore

section Glue

theorem isPGroup_of_isElemAbelian {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) : IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h1 : ∀ x ∈ H, g * x * g⁻¹ ∈ H) (h2 : ∀ x ∈ H, g⁻¹ * x * g ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rwa [e] at this

theorem normalizer_inf_centralizer {G : Type*} [Group G] {p : ℕ} {B X : Subgroup G}
    (hB : IsElemAbelian p B) (hBX : B ≤ Subgroup.normalizer (X : Set G)) {b : G} (hb : b ∈ B) :
    B ≤ Subgroup.normalizer ((X ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) : Set G) := by
  have hc := hB.1
  have key : ∀ β ∈ B, ∀ x ∈ X ⊓ Subgroup.centralizer ({b} : Set G),
      β * x * β⁻¹ ∈ X ⊓ Subgroup.centralizer ({b} : Set G) := by
    intro β hβ x hx
    obtain ⟨hxX, hxc⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hBX hβ) x).1 hxX, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxc ⊢
    have hbβ : Commute b β := congrArg Subtype.val (mul_comm' (⟨b, hb⟩ : B) ⟨β, hβ⟩)
    have hbx : Commute b x := hxc.symm
    exact ((hbβ.mul_right hbx).mul_right hbβ.inv_right).eq.symm
  intro β hβ
  exact mem_normalizer_of_conj_mem (key β hβ) (by simpa using key β⁻¹ (inv_mem hβ))

theorem na_case (h713 : I_7_13_1_pPrime) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G : Type} [Group G] [Finite G] {B X D : Subgroup G}
    (hB : IsElemAbelian p B) (hBX : B ≤ Subgroup.normalizer (X : Set G))
    (hX : ¬ p ∣ Nat.card X) (hXK : IsKGroup ↥X) (hDB : D ≤ B)
    (hB2 : p ^ 2 ≤ Nat.card B) (hfaith : B ⊓ Subgroup.centralizer (X : Set G) = ⊥)
    (hX1 : X ≠ ⊥) (hns : ¬ Group.IsSolvable ↥X)
    (hmin : ∀ M : Subgroup G, M ≤ X → X ≤ Subgroup.normalizer (M : Set G) →
      B ≤ Subgroup.normalizer (M : Set G) → M = ⊥ ∨ M = X) :
    ⁅X, D⁆ ≤ ⨆ (b : G) (_ : b ∈ B ∧ b ≠ 1), ⁅X ⊓ Subgroup.centralizer ({b} : Set G), D⁆ := by
  obtain ⟨d⟩ := exists_factorData h713 hp hp2 hB hBX hX hXK hfaith hX1 hns hmin
  exact d.na_core hp hp2 hB hDB hB2

theorem main_aux (h713 : I_7_13_1_pPrime) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ n m, Claim p n m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihB =>
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihX =>
  intro G _ _ B X D hBn hXm hB hBX hX hXK hDB
  have ihB' : ∀ n' < Nat.card B, ∀ m', Claim p n' m' := fun n' hn' m' =>
    ihB n' (hBn ▸ hn') m'
  by_cases hsmall : Nat.card B ≤ p
  · exact comm_le_hyperplaneJoin_of_card_le hsmall
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian hB
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hBp.exists_card_eq
  have hB2 : p ^ 2 ≤ Nat.card B := by
    have hk2 : 2 ≤ k := by
      by_contra hk2
      refine hsmall ?_
      rw [hk]
      calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
        _ = p := pow_one p
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos hk2
  by_cases hfaith : B ⊓ Subgroup.centralizer (X : Set G) = ⊥
  swap
  · exact reduce_B hp hB hBX hDB inf_le_left inf_le_right hfaith hX hXK ihB'
  by_cases hX1 : X = ⊥
  · subst hX1
    simp
  have hDX : D ≤ Subgroup.normalizer (X : Set G) := hDB.trans hBX
  have hDp : IsPGroup p D := hBp.to_le hDB
  set Y : Subgroup G := ⁅X, D⁆ with hYdef
  by_cases hY : Y = X
  swap
  · have hYX : Y ≤ X := comm_le_of_le_normalizer hDX
    have hlt : Nat.card Y < m := by
      rw [← hXm]
      exact Subgroup.card_lt_of_lt (lt_of_le_of_ne hYX hY)
    have hih := ihX (Nat.card Y) hlt G B Y D hBn rfl hB (normalizer_comm hB hBX hDB)
      (fun h => hX (h.trans (Subgroup.card_dvd_of_le hYX)))
      (isKGroup_of_le hXK hYX) hDB
    calc Y = ⁅Y, D⁆ := (comm_comm_eq hp hDp hDX hX).symm
      _ ≤ hyperplaneJoin p B Y D := hih
      _ ≤ hyperplaneJoin p B X D := hyperplaneJoin_mono hYX
  obtain ⟨N, hNX, hXN, hBN, hN1, hNmin⟩ := exists_minimal_invariant_normal hX1 hBX
  by_cases hNeq : N = X
  · subst hNeq
    by_cases hs : Group.IsSolvable ↥N
    · exact solv_case hp hB hB2 hBX hX hs hDB
    · have h1 := na_case h713 hp hp2 hB hBX hX hXK hDB hB2 hfaith hX1 hs
        (fun M hMX hXM hBM => hNmin M hMX hXM hBM)
      refine h1.trans (iSup₂_le fun b hb => ?_)
      have hbB : b ∈ B := hb.1
      have hYX : N ⊓ Subgroup.centralizer ({b} : Set G) ≤ N := inf_le_left
      have hih := reduce_B hp hB (normalizer_inf_centralizer hB hBX hbB) hDB
        (Subgroup.zpowers_le.2 hbB)
        (by
          rw [Subgroup.zpowers_le]
          exact Subgroup.mem_centralizer_iff.2 fun y hy =>
            (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hy).2))
        (fun h => hb.2 (Subgroup.zpowers_eq_bot.1 h))
        (fun h => hX (h.trans (Subgroup.card_dvd_of_le hYX)))
        (isKGroup_of_le hXK hYX) ihB'
      exact hih.trans (hyperplaneJoin_mono hYX)
  · have hNlt : N < X := lt_of_le_of_ne hNX hNeq
    obtain ⟨G', _, _, B', X', D', hB'n, hX'lt, hB', hB'X', hX', hX'K, hD'B', himp⟩ :=
      quot_transfer hp hB hBX hX hXK hDB hNX hXN hBN hN1
    have hih := ihX (Nat.card X') (hXm ▸ hX'lt) G' B' X' D' (hB'n.trans hBn) rfl hB' hB'X' hX'
      hX'K hD'B'
    have h1 : ⁅X, D⁆ ≤ hyperplaneJoin p B X D ⊔ N := himp hih
    have hNcard : Nat.card N < m := by
      rw [← hXm]
      exact Subgroup.card_lt_of_lt hNlt
    have hih2 := ihX (Nat.card N) hNcard G B N D hBn rfl hB hBN
      (fun h => hX (h.trans (Subgroup.card_dvd_of_le hNX))) (isKGroup_of_le hXK hNX) hDB
    have h2 : ⁅N, D⁆ ≤ hyperplaneJoin p B X D := hih2.trans (hyperplaneJoin_mono hNX)
    exact comm_le_of_comm_le_sup hXN (hyperplaneJoin_le hDX)
      (hDB.trans (normalizer_hyperplaneJoin hB hBX hDB)) (hY.symm.le.trans h1) h2

end Glue

end Generation228

theorem commutator_eq_iSup_commutator_centralizer (h713 : I_7_13_1_pPrime)
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B X D : Subgroup G}
    (hB : IsElemAbelian p B) (hBX : B ≤ Subgroup.normalizer (X : Set G))
    (hX : ¬ p ∣ Nat.card X) (hXK : CFSG.Open.IsKGroup ↥X) (hDB : D ≤ B) :
    ⁅X, D⁆ = ⨆ (A : Subgroup G) (_ : A ≤ B ∧ (A.subgroupOf B).index ≤ p),
      ⁅X ⊓ Subgroup.centralizer (A : Set G), D⁆ :=
  le_antisymm (Generation228.main_aux h713 hp hp2 _ _ G B X D rfl rfl hB hBX hX hXK hDB)
    Generation228.hyperplaneJoin_le_comm

end CFSG.HardMathSupport.Solomon.Coordinator
