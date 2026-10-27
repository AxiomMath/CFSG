module

public import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

theorem sq_commutator_mem_of_card_three_mul {X : Type*} [Group X] [Finite X]
    {E F : Subgroup X} (hEF : E ≤ F) (hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hcard : Nat.card F = 3 * Nat.card E) {s : X}
    (hsE : ∀ e ∈ E, s * e * s⁻¹ ∈ E) (hsF : ∀ f ∈ F, s * f * s⁻¹ ∈ F) :
    ∀ f ∈ F, s ^ 2 * f * (s ^ 2)⁻¹ * f⁻¹ ∈ E := by
  have hinv : ∀ (H : Subgroup X), (∀ h ∈ H, s * h * s⁻¹ ∈ H) → ∀ h ∈ H, s⁻¹ * h * s ∈ H := by
    intro H hH h hh
    have hinj : Function.Injective (fun y : H => (⟨s * y * s⁻¹, hH y y.2⟩ : H)) := by
      intro a b hab
      apply Subtype.ext
      have := congrArg Subtype.val hab
      simpa using this
    obtain ⟨y, hy⟩ := (Finite.surjective_of_injective hinj) ⟨h, hh⟩
    have hyy : s * (y : X) * s⁻¹ = h := congrArg Subtype.val hy
    rw [← hyy]
    simp [mul_assoc]
  have hsE' := hinv E hsE
  have hsF' := hinv F hsF
  have : IsMulCommutative F := ⟨⟨fun a b => Subtype.ext (hFab a a.2 b b.2)⟩⟩
  let σ : F ≃* F :=
    { toFun := fun x => ⟨s * x * s⁻¹, hsF x x.2⟩
      invFun := fun x => ⟨s⁻¹ * x * s, hsF' x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hmap : (E.subgroupOf F).map (σ : F →* F) = E.subgroupOf F := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hsE y hy
    · intro hx
      exact ⟨σ.symm x, hsE' x hx, σ.apply_symm_apply x⟩
  let α : MulAut (F ⧸ E.subgroupOf F) :=
    QuotientGroup.congr (E.subgroupOf F) (E.subgroupOf F) σ hmap
  have hE'card : Nat.card (E.subgroupOf F) = Nat.card E := by
    rw [← Subgroup.card_subtype F (E.subgroupOf F), Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hEF]
  have hQ : Nat.card (F ⧸ E.subgroupOf F) = 3 := by
    have h1 := Subgroup.card_mul_index (E.subgroupOf F)
    rw [hE'card, hcard] at h1
    have hpos : 0 < Nat.card E := Nat.card_pos
    have h2 : Nat.card E * (E.subgroupOf F).index = Nat.card E * 3 := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  have hcyc : IsCyclic (F ⧸ E.subgroupOf F) := isCyclic_of_prime_card hQ
  have hAut : Nat.card (MulAut (F ⧸ E.subgroupOf F)) = 2 := by
    rw [IsCyclic.card_mulAut, hQ, Nat.totient_prime Nat.prime_three]
  have hα2 : ∀ q, α (α q) = q := by
    intro q
    have h := pow_card_eq_one' (x := α)
    rw [hAut, pow_two] at h
    simpa using congrArg (fun φ : MulAut (F ⧸ E.subgroupOf F) => φ q) h
  intro f hf
  have h := hα2 (QuotientGroup.mk (⟨f, hf⟩ : F))
  have h' : (QuotientGroup.mk (σ (σ ⟨f, hf⟩)) : F ⧸ E.subgroupOf F) = QuotientGroup.mk ⟨f, hf⟩ :=
    h
  have hmem := QuotientGroup.eq.1 h'
  rw [Subgroup.mem_subgroupOf] at hmem
  have hu : s * (s * f * s⁻¹) * s⁻¹ ∈ F := hsF _ (hsF f hf)
  have e1 : s ^ 2 * f * (s ^ 2)⁻¹ = s * (s * f * s⁻¹) * s⁻¹ := by simp [pow_two, mul_assoc]
  rw [e1, hFab _ hu _ (inv_mem hf)]
  have e2 : f⁻¹ * (s * (s * f * s⁻¹) * s⁻¹) = ((s * (s * f * s⁻¹) * s⁻¹)⁻¹ * f)⁻¹ := by
    rw [mul_inv_rev, inv_inv]
  rw [e2]
  exact inv_mem hmem

theorem centralizes_of_trivial_action_of_rigid {X : Type*} [Group X] [Finite X]
    {E F : Subgroup X} (hFn : F.Normal) (hEF : E ≤ F) (hF3 : ∀ f ∈ F, f ^ 3 = 1)
    (hrig : ∀ g : X, (∃ k : ℕ, g ^ 3 ^ k = 1) → (∀ e ∈ E, g * e * g⁻¹ = e) →
      (∀ f ∈ F, g * f * g⁻¹ * f⁻¹ ∈ E) → ∀ f ∈ F, g * f * g⁻¹ = f)
    {v : X} (hvE : ∀ e ∈ E, v * e * v⁻¹ = e) (hvF : ∀ f ∈ F, v * f * v⁻¹ * f⁻¹ ∈ E) :
    ∀ f ∈ F, v * f * v⁻¹ = f := by
  let K : Subgroup X :=
    { carrier := {g | (∀ e ∈ E, g * e * g⁻¹ = e) ∧ ∀ f ∈ F, g * f * g⁻¹ * f⁻¹ ∈ E}
      one_mem' := ⟨fun e _ => by simp, fun f _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨fun e he => ?_, fun f hf => ?_⟩
        · calc a * b * e * (a * b)⁻¹ = a * (b * e * b⁻¹) * a⁻¹ := by group
            _ = e := by rw [hb1 e he, ha1 e he]
        · have h1 : a * b * f * (a * b)⁻¹ * f⁻¹ =
              (a * (b * f * b⁻¹ * f⁻¹) * a⁻¹) * (a * f * a⁻¹ * f⁻¹) := by group
          rw [h1, ha1 _ (hb2 f hf)]
          exact E.mul_mem (hb2 f hf) (ha2 f hf)
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        refine ⟨fun e he => ?_, fun f hf => ?_⟩
        · calc a⁻¹ * e * a⁻¹⁻¹ = a⁻¹ * (a * e * a⁻¹) * a⁻¹⁻¹ := by rw [ha1 e he]
            _ = e := by group
        · have hf' : a⁻¹ * f * a⁻¹⁻¹ ∈ F := hFn.conj_mem f hf a⁻¹
          have h1 : a⁻¹ * f * a⁻¹⁻¹ * f⁻¹ =
              (a * (a⁻¹ * f * a⁻¹⁻¹) * a⁻¹ * (a⁻¹ * f * a⁻¹⁻¹)⁻¹)⁻¹ := by group
          rw [h1]
          exact E.inv_mem (ha2 _ hf') }
  have hvK : v ∈ K := ⟨hvE, hvF⟩
  have hC : ∀ g : X, g ∈ Subgroup.centralizer (F : Set X) ↔ ∀ f ∈ F, g * f * g⁻¹ = f := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    refine forall₂_congr fun f _ => ?_
    rw [mul_inv_eq_iff_eq_mul, eq_comm]
  have hcube : v ^ 3 ∈ Subgroup.centralizer (F : Set X) := by
    rw [hC]
    intro f hf
    have hv3 : v ^ 3 = v * v * v := by rw [pow_succ, pow_two]
    have h1 : v * (v * (v * f * v⁻¹) * v⁻¹) * v⁻¹ = v ^ 3 * f * (v ^ 3)⁻¹ := by
      rw [hv3]; simp [mul_assoc]
    obtain ⟨e, he, hef⟩ : ∃ e ∈ E, v * f * v⁻¹ = e * f :=
      ⟨v * f * v⁻¹ * f⁻¹, hvF f hf, by group⟩
    have h2 : v * (e * f) * v⁻¹ = e * (e * f) := by
      rw [show v * (e * f) * v⁻¹ = (v * e * v⁻¹) * (v * f * v⁻¹) by group, hvE e he, hef]
    have h3 : v * (e * (e * f)) * v⁻¹ = e * (e * (e * f)) := by
      rw [show v * (e * (e * f)) * v⁻¹ = (v * e * v⁻¹) * (v * (e * f) * v⁻¹) by group,
        hvE e he, h2]
    rw [← h1, hef, h2, h3]
    have he3 : e ^ 3 = 1 := hF3 e (hEF he)
    calc e * (e * (e * f)) = e ^ 3 * f := by rw [pow_succ, pow_two]; simp only [mul_assoc]
      _ = f := by rw [he3, one_mul]
  obtain ⟨k, m, hm, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos v).ne' 3 (by norm_num)
  have hgK : v ^ m ∈ K := K.pow_mem hvK m
  have hg : v ^ m ∈ Subgroup.centralizer (F : Set X) := by
    rw [hC]
    refine hrig (v ^ m) ⟨k, ?_⟩ hgK.1 hgK.2
    rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hcop : Nat.gcd 3 m = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm
  have hbez := Nat.gcd_eq_gcd_ab 3 m
  rw [hcop] at hbez
  have hv : v ∈ Subgroup.centralizer (F : Set X) := by
    have h1 : v = (v ^ m) ^ Nat.gcdB 3 m * (v ^ 3) ^ Nat.gcdA 3 m := by
      have hab : (m : ℤ) * Nat.gcdB 3 m + (3 : ℤ) * Nat.gcdA 3 m = 1 := by
        push_cast at hbez
        rw [add_comm]
        exact hbez.symm
      have := zpow_add v ((m : ℤ) * Nat.gcdB 3 m) ((3 : ℤ) * Nat.gcdA 3 m)
      rw [hab, zpow_one, zpow_mul, zpow_mul] at this
      simpa using this
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hg _) (Subgroup.zpow_mem _ hcube _)
  exact (hC v).1 hv

theorem exists_fixed_subgroup_card_three_of_inverting {X : Type*} [Group X] [Finite X]
    {E F : Subgroup X} (hEF : E ≤ F) (hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hF3 : ∀ f ∈ F, f ^ 3 = 1) (hE : Nat.card E = 9) (hF : Nat.card F = 27) {z : X}
    (hzE : ∀ e ∈ E, z * e * z⁻¹ = e⁻¹) (hzF : ∀ f ∈ F, z * f * z⁻¹ * f⁻¹ ∈ E) :
    ∃ P : Subgroup X, P ≤ F ∧ (∀ f, f ∈ P ↔ f ∈ F ∧ z * f * z⁻¹ = f) ∧ Nat.card P = 3 := by
  let θ : F →* E :=
    { toFun := fun f => ⟨z * f * z⁻¹ * f⁻¹, hzF f f.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        have hb : z * (b : X) * z⁻¹ * (b : X)⁻¹ ∈ F := hEF (hzF b b.2)
        have hc : (z * (b : X) * z⁻¹ * (b : X)⁻¹) * (a : X)⁻¹ =
            (a : X)⁻¹ * (z * (b : X) * z⁻¹ * (b : X)⁻¹) := hFab _ hb _ (F.inv_mem a.2)
        calc z * ((a : X) * b) * z⁻¹ * ((a : X) * b)⁻¹
            = (z * a * z⁻¹) * ((z * (b : X) * z⁻¹ * (b : X)⁻¹) * (a : X)⁻¹) := by group
          _ = (z * a * z⁻¹ * (a : X)⁻¹) * (z * (b : X) * z⁻¹ * (b : X)⁻¹) := by
            rw [hc]; group }
  have hsurj : Function.Surjective θ := by
    rintro ⟨e, he⟩
    refine ⟨⟨e, hEF he⟩, Subtype.ext ?_⟩
    show z * e * z⁻¹ * e⁻¹ = e
    rw [hzE e he, ← mul_inv_rev, inv_eq_iff_mul_eq_one]
    have h3 : e ^ 3 = 1 := hF3 e (hEF he)
    rwa [pow_succ, pow_two] at h3
  have hcard := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [hE, hF] at hcard
  have hker : Nat.card θ.ker = 3 := by omega
  refine ⟨θ.ker.map F.subtype, Subgroup.map_subtype_le _, fun f => ?_, ?_⟩
  · simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      have := congrArg Subtype.val hy
      simpa [θ, mul_inv_eq_one] using this
    · rintro ⟨hf, hz⟩
      refine ⟨⟨f, hf⟩, ?_, rfl⟩
      apply Subtype.ext
      simp [θ, hz]
  · rw [Subgroup.card_subtype]
    exact hker

theorem exists_normal_of_inverting {X : Type*} [Group X] [Finite X]
    {E F : Subgroup X} (hEn : E.Normal) (hFn : F.Normal) (hEF : E ≤ F)
    (hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) (hF3 : ∀ f ∈ F, f ^ 3 = 1)
    (hE : Nat.card E = 9) (hF : Nat.card F = 27)
    {z : X} (hzE : ∀ e ∈ E, z * e * z⁻¹ = e⁻¹)
    (hzF : ∀ f ∈ F, z * f * z⁻¹ * f⁻¹ ∈ E)
    (hrig : ∀ g : X, (∃ k : ℕ, g ^ 3 ^ k = 1) → (∀ e ∈ E, g * e * g⁻¹ = e) →
      (∀ f ∈ F, g * f * g⁻¹ * f⁻¹ ∈ E) → ∀ f ∈ F, g * f * g⁻¹ = f) :
    ∃ P : Subgroup X, P.Normal ∧ P ≤ F ∧ Nat.card P = 3 := by
  obtain ⟨P, hPF, hPmem, hPcard⟩ :=
    exists_fixed_subgroup_card_three_of_inverting hEF hFab hF3 hE hF hzE hzF
  refine ⟨P, ⟨fun n hn x => ?_⟩, hPF, hPcard⟩
  rw [hPmem] at hn ⊢
  obtain ⟨hnF, hzn⟩ := hn
  refine ⟨hFn.conj_mem n hnF x, ?_⟩
  have hvE : ∀ e ∈ E, (x⁻¹ * z * x * z⁻¹) * e * (x⁻¹ * z * x * z⁻¹)⁻¹ = e := by
    intro e he
    have h1 : z⁻¹ * e * z = e⁻¹ := by
      have h := hzE e⁻¹ (E.inv_mem he)
      rw [inv_inv] at h
      calc z⁻¹ * e * z = z⁻¹ * (z * e⁻¹ * z⁻¹) * z := by rw [h]
        _ = e⁻¹ := by group
    have h2 : z * (x * e⁻¹ * x⁻¹) * z⁻¹ = x * e * x⁻¹ := by
      rw [hzE _ (hEn.conj_mem _ (E.inv_mem he) x)]
      group
    calc x⁻¹ * z * x * z⁻¹ * e * (x⁻¹ * z * x * z⁻¹)⁻¹
        = x⁻¹ * (z * (x * (z⁻¹ * e * z) * x⁻¹) * z⁻¹) * x := by group
      _ = x⁻¹ * (z * (x * e⁻¹ * x⁻¹) * z⁻¹) * x := by rw [h1]
      _ = e := by rw [h2]; group
  have hvF : ∀ f ∈ F, (x⁻¹ * z * x * z⁻¹) * f * (x⁻¹ * z * x * z⁻¹)⁻¹ * f⁻¹ ∈ E := by
    intro f hf
    have hf1 : z⁻¹ * f * z ∈ F := by simpa using hFn.conj_mem f hf z⁻¹
    have ha : f * (z⁻¹ * f * z)⁻¹ ∈ E := by
      have h := hzF _ hf1
      have e1 : z * (z⁻¹ * f * z) * z⁻¹ * (z⁻¹ * f * z)⁻¹ = f * (z⁻¹ * f * z)⁻¹ := by group
      rwa [e1] at h
    have hb : x⁻¹ * z * x * (z⁻¹ * f * z) * (x⁻¹ * z * x)⁻¹ * (z⁻¹ * f * z)⁻¹ ∈ E := by
      have hxf : x * (z⁻¹ * f * z) * x⁻¹ ∈ F := hFn.conj_mem _ hf1 x
      have h := hEn.conj_mem _ (hzF _ hxf) x⁻¹
      have e1 : x⁻¹ * (z * (x * (z⁻¹ * f * z) * x⁻¹) * z⁻¹ * (x * (z⁻¹ * f * z) * x⁻¹)⁻¹) *
          x⁻¹⁻¹ = x⁻¹ * z * x * (z⁻¹ * f * z) * (x⁻¹ * z * x)⁻¹ * (z⁻¹ * f * z)⁻¹ := by group
      rwa [e1] at h
    have e2 : x⁻¹ * z * x * z⁻¹ * f * (x⁻¹ * z * x * z⁻¹)⁻¹ * f⁻¹ =
        (x⁻¹ * z * x * (z⁻¹ * f * z) * (x⁻¹ * z * x)⁻¹ * (z⁻¹ * f * z)⁻¹) *
          (f * (z⁻¹ * f * z)⁻¹)⁻¹ := by group
    rw [e2]
    exact E.mul_mem hb (E.inv_mem ha)
  have hv := centralizes_of_trivial_action_of_rigid hFn hEF hF3 hrig hvE hvF n hnF
  have h1 : (x⁻¹ * z * x * z⁻¹) * (z * n * z⁻¹) * (x⁻¹ * z * x * z⁻¹)⁻¹ = n := by
    rw [hzn]; exact hv
  calc z * (x * n * x⁻¹) * z⁻¹
      = x * ((x⁻¹ * z * x * z⁻¹) * (z * n * z⁻¹) * (x⁻¹ * z * x * z⁻¹)⁻¹) * x⁻¹ := by group
    _ = x * n * x⁻¹ := by rw [h1]

end CFSG.LocalAnalysis.RankThreeTheoremC
