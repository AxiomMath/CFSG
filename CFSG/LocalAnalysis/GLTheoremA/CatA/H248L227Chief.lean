module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248L227QK
public import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Data.Nat.Choose.Dvd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248L227

section Tools

variable {X : Type*} [Group X]

private theorem comm_of_comm_central (hperf : commutator X = ⊤) {u : X}
    (hu : ∀ g : X, g * u * g⁻¹ * u⁻¹ ∈ Subgroup.center X) (g : X) : g * u = u * g := by
  let f : X →* Subgroup.center X :=
    MonoidHom.mk' (fun g => ⟨g * u * g⁻¹ * u⁻¹, hu g⟩) (by
      intro g h
      apply Subtype.ext
      have e1 : g * (h * u * h⁻¹ * u⁻¹) = (h * u * h⁻¹ * u⁻¹) * g :=
        Subgroup.mem_center_iff.mp (hu h) g
      have e2 : (g * u * g⁻¹ * u⁻¹) * (h * u * h⁻¹ * u⁻¹) =
          (h * u * h⁻¹ * u⁻¹) * (g * u * g⁻¹ * u⁻¹) :=
        Subgroup.mem_center_iff.mp (hu h) _
      show g * h * u * (g * h)⁻¹ * u⁻¹ = (g * u * g⁻¹ * u⁻¹) * (h * u * h⁻¹ * u⁻¹)
      calc g * h * u * (g * h)⁻¹ * u⁻¹
          = g * (h * u * h⁻¹ * u⁻¹) * (u * g⁻¹ * u⁻¹) := by group
        _ = (h * u * h⁻¹ * u⁻¹) * g * (u * g⁻¹ * u⁻¹) := by rw [e1]
        _ = (h * u * h⁻¹ * u⁻¹) * (g * u * g⁻¹ * u⁻¹) := by group
        _ = (g * u * g⁻¹ * u⁻¹) * (h * u * h⁻¹ * u⁻¹) := e2.symm)
  have hker : f.ker = ⊤ := by
    have := Abelianization.commutator_subset_ker f
    rw [hperf] at this
    exact top_le_iff.mp this
  have h1 : g ∈ f.ker := by rw [hker]; exact Subgroup.mem_top g
  have h2 : g * u * g⁻¹ * u⁻¹ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp h1)
  calc g * u = (g * u * g⁻¹ * u⁻¹) * (u * g) := by group
    _ = u * g := by rw [h2, one_mul]

private theorem centralizes_of_quot (hperf : commutator X = ⊤) {U : Subgroup X}
    (h : ∀ u ∈ U, ∀ g : X, u⁻¹ * (g * u * g⁻¹) ∈ Subgroup.center X) :
    ∀ u ∈ U, ∀ g : X, g * u = u * g := by
  intro u hu g
  refine comm_of_comm_central hperf (fun g => ?_) g
  have hc := h u hu g
  have e : g * u * g⁻¹ * u⁻¹ = u * (u⁻¹ * (g * u * g⁻¹)) * u⁻¹ := by group
  have e2 : u * (u⁻¹ * (g * u * g⁻¹)) * u⁻¹ = u⁻¹ * (g * u * g⁻¹) := by
    rw [Subgroup.mem_center_iff.mp hc u]
    group
  rw [e, e2]
  exact hc

private theorem mul_pow_of_commute {a b : X} (ha : Commute (b * a * b⁻¹ * a⁻¹) a)
    (hb : Commute (b * a * b⁻¹ * a⁻¹) b) (n : ℕ) :
    (a * b) ^ n = (b * a * b⁻¹ * a⁻¹) ^ n.choose 2 * (a ^ n * b ^ n) := by
  set c := b * a * b⁻¹ * a⁻¹ with hc
  have hba : b * a = c * (a * b) := by rw [hc]; group
  have hbn : ∀ n : ℕ, b ^ n * a = c ^ n * (a * b ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc b ^ (n + 1) * a = b * (b ^ n * a) := by rw [pow_succ', mul_assoc]
        _ = b * (c ^ n * (a * b ^ n)) := by rw [ih]
        _ = (b * c ^ n) * (a * b ^ n) := by rw [mul_assoc]
        _ = (c ^ n * b) * (a * b ^ n) := by rw [(hb.pow_left n).symm.eq]
        _ = c ^ n * (b * a) * b ^ n := by simp only [mul_assoc]
        _ = c ^ n * (c * (a * b)) * b ^ n := by rw [hba]
        _ = c ^ (n + 1) * (a * b ^ (n + 1)) := by
          rw [pow_succ c n, pow_succ' b n]
          simp only [mul_assoc]
  induction n with
  | zero => simp
  | succ n ih =>
    have hC : (n + 1).choose 2 = n.choose 2 + n := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring
    calc (a * b) ^ (n + 1) = (a * b) ^ n * (a * b) := pow_succ _ _
      _ = c ^ n.choose 2 * (a ^ n * b ^ n) * (a * b) := by rw [ih]
      _ = c ^ n.choose 2 * (a ^ n * (b ^ n * a) * b) := by simp only [mul_assoc]
      _ = c ^ n.choose 2 * (a ^ n * (c ^ n * (a * b ^ n)) * b) := by rw [hbn n]
      _ = c ^ n.choose 2 * (c ^ n * (a ^ n * a * (b ^ n * b))) := by
        have : a ^ n * (c ^ n * (a * b ^ n)) * b = c ^ n * (a ^ n * a * (b ^ n * b)) := by
          calc a ^ n * (c ^ n * (a * b ^ n)) * b
              = (a ^ n * c ^ n) * (a * b ^ n) * b := by simp only [mul_assoc]
            _ = (c ^ n * a ^ n) * (a * b ^ n) * b := by rw [(ha.pow_pow n n).eq.symm]
            _ = c ^ n * (a ^ n * a * (b ^ n * b)) := by simp only [mul_assoc]
        rw [this]
      _ = c ^ (n + 1).choose 2 * (a ^ (n + 1) * b ^ (n + 1)) := by
        rw [hC, pow_add c (n.choose 2) n, pow_succ a n, pow_succ b n]
        simp only [mul_assoc]

private theorem comm_pow_eq_one {a b : X} {n : ℕ} (ha : Commute (b * a * b⁻¹ * a⁻¹) a)
    (hcen : ∀ y : X, y * a ^ n = a ^ n * y) : (b * a * b⁻¹ * a⁻¹) ^ n = 1 := by
  set c := b * a * b⁻¹ * a⁻¹ with hc
  have h2 : b * a * b⁻¹ = c * a := by rw [hc]; group
  have h4 : b * a ^ n * b⁻¹ = a ^ n := by rw [hcen b]; group
  have h5 : c ^ n * a ^ n = 1 * a ^ n := by
    rw [← ha.mul_pow n, ← h2, conj_pow, h4, one_mul]
  exact mul_right_cancel h5

private theorem exists_pow_subgroup (U M : Subgroup X) [U.Normal] [M.Normal] (n : ℕ)
    (hmul : ∀ a ∈ U, ∀ b ∈ U, a ^ n ∈ M → b ^ n ∈ M → (a * b) ^ n ∈ M) :
    ∃ P : Subgroup X, P.Normal ∧ ∀ u : X, u ∈ P ↔ u ∈ U ∧ u ^ n ∈ M := by
  let P : Subgroup X :=
    { carrier := {u | u ∈ U ∧ u ^ n ∈ M}
      mul_mem' := fun {a b} ha hb => ⟨U.mul_mem ha.1 hb.1, hmul a ha.1 b hb.1 ha.2 hb.2⟩
      one_mem' := ⟨U.one_mem, by simpa using M.one_mem⟩
      inv_mem' := fun {a} ha => ⟨U.inv_mem ha.1, by simpa [inv_pow] using M.inv_mem ha.2⟩ }
  refine ⟨P, ⟨fun a ha g => ?_⟩, fun u => Iff.rfl⟩
  refine ⟨(inferInstance : U.Normal).conj_mem a ha.1 g, ?_⟩
  have h := (inferInstance : M.Normal).conj_mem _ ha.2 g
  simpa [conj_pow] using h

private theorem commutator_lt_of_isPGroup [Finite X] {q : ℕ} (hq : q.Prime) {U : Subgroup X}
    (hU : IsPGroup q U) (hne : U ≠ ⊥) : ⁅U, U⁆ < U := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Group.IsNilpotent U := hU.isNilpotent
  haveI : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot U).mpr hne
  have h := Group.IsSolvable.commutator_lt_top_of_nontrivial U
  rw [← U.range_subtype, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
    Subgroup.map_subtype_lt_map_subtype]
  exact h

private theorem exists_pow_mem_of_pow_eq_one {q : ℕ} (C : Subgroup X) {u : X} (hu : u ∉ C)
    {m : ℕ} (hm : u ^ q ^ m = 1) : ∃ k : ℕ, u ^ q ^ k ∉ C ∧ (u ^ q ^ k) ^ q ∈ C := by
  induction m generalizing u with
  | zero =>
    exfalso
    apply hu
    have h1 : u = 1 := by simpa using hm
    rw [h1]
    exact C.one_mem
  | succ m ih =>
    by_cases h : u ^ q ∈ C
    · exact ⟨0, by simpa using hu, by simpa using h⟩
    · have hm' : (u ^ q) ^ q ^ m = 1 := by rw [← pow_mul, ← pow_succ']; exact hm
      obtain ⟨k, hk1, hk2⟩ := ih h hm'
      exact ⟨k + 1, by rwa [pow_succ', pow_mul], by rwa [pow_succ', pow_mul]⟩

end Tools

section Abelian

variable {X : Type*} [Group X]

private theorem zpowers_comm (w : X) :
    ∀ a ∈ Subgroup.zpowers w, ∀ b ∈ Subgroup.zpowers w, a * b = b * a := by
  intro a ha b hb
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact (Commute.zpow_zpow_self w i j).eq

private theorem zpowers_comm_of_commute {w : X} {A : Subgroup X} (h : ∀ a ∈ A, a * w = w * a) :
    ∀ a ∈ A, ∀ b ∈ Subgroup.zpowers w, a * b = b * a := by
  intro a ha b hb
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hc : Commute a w := h a ha
  exact (hc.zpow_right j).eq

private theorem sup_comm_aux {A₁ A₂ : Subgroup X} (h1 : ∀ a ∈ A₁, ∀ b ∈ A₁, a * b = b * a)
    (h2 : ∀ a ∈ A₂, ∀ b ∈ A₂, a * b = b * a) (h12 : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) :
    ∀ a ∈ A₁ ⊔ A₂, ∀ b ∈ A₁ ⊔ A₂, a * b = b * a := by
  have s1 : ∀ a ∈ A₁, A₁ ⊔ A₂ ≤ Subgroup.centralizer {a} := by
    intro a ha
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (h1 x hx a ha)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (h12 a ha x hx).symm
  have s2 : ∀ a ∈ A₂, A₁ ⊔ A₂ ≤ Subgroup.centralizer {a} := by
    intro a ha
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (h12 x hx a ha)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (h2 x hx a ha)
  intro a ha
  have hle : A₁ ⊔ A₂ ≤ Subgroup.centralizer {a} := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_singleton_iff.1 (s1 x hx ha)).symm
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_singleton_iff.1 (s2 x hx ha)).symm
  intro b hb
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hb)).symm

private theorem q_mul_card_le [Finite X] {q : ℕ} (hq : q.Prime) {U A B : Subgroup X}
    (hexp : ∀ u ∈ U, u ^ q = 1) (hAB : A ≤ B) (hBU : B ≤ U) (hne : A ≠ B) :
    q * Nat.card A ≤ Nat.card B := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hB : IsPGroup q B := fun b => ⟨1, by rw [pow_one]; exact Subtype.ext (hexp b (hBU b.2))⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hB
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hAB
  have hkd : k ∣ q ^ n := ⟨Nat.card A, by rw [← hn, hk, mul_comm]⟩
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hq).1 hkd
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact absurd (Subgroup.eq_of_le_of_card_ge hAB (by rw [hk]; simp)) hne
  · rw [hk, mul_comm (Nat.card A)]
    exact Nat.mul_le_mul_right _ (Nat.le_self_pow hj.ne' q)

private theorem mem_of_commute_of_card [Finite X] {q : ℕ} {U A : Subgroup X}
    (hab : ∀ A : Subgroup X, A ≤ U → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A ≤ q ^ 3)
    (hAU : A ≤ U) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hcard : q ^ 3 ≤ Nat.card A)
    {w : X} (hw : w ∈ U) (hwA : ∀ a ∈ A, a * w = w * a) : w ∈ A := by
  have hsup := sup_comm_aux hA (zpowers_comm w) (zpowers_comm_of_commute hwA)
  have h1 := hab (A ⊔ Subgroup.zpowers w) (sup_le hAU (Subgroup.zpowers_le.2 hw)) hsup
  have heq : A = A ⊔ Subgroup.zpowers w :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (h1.trans hcard)
  have hmem : w ∈ A ⊔ Subgroup.zpowers w := Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  rwa [← heq] at hmem

private theorem card_le_inf_centralizer_mul [Finite X] {U : Subgroup X}
    (hcl : ∀ a ∈ U, ∀ b ∈ U, ∀ c ∈ U, a * b * a⁻¹ * b⁻¹ * c = c * (a * b * a⁻¹ * b⁻¹))
    {Z : Subgroup X} (hZ : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Z)
    {S : Subgroup X} (hS : S ≤ U) {y : X} (hy : y ∈ U) :
    Nat.card S ≤ Nat.card (S ⊓ Subgroup.centralizer {y} : Subgroup X) * Nat.card Z := by
  let f : S →* Z :=
    MonoidHom.mk' (fun s => ⟨y * (s : X) * y⁻¹ * (s : X)⁻¹, hZ y hy s (hS s.2)⟩) (by
      intro s t
      apply Subtype.ext
      have h1 := hcl y hy t (hS t.2) s (hS s.2)
      show y * ((s : X) * t) * y⁻¹ * ((s : X) * t)⁻¹ =
        (y * s * y⁻¹ * (s : X)⁻¹) * (y * t * y⁻¹ * (t : X)⁻¹)
      calc y * ((s : X) * t) * y⁻¹ * ((s : X) * t)⁻¹
          = (y * s * y⁻¹ * (s : X)⁻¹) * ((s : X) * (y * t * y⁻¹ * (t : X)⁻¹) * (s : X)⁻¹) := by
            group
        _ = (y * s * y⁻¹ * (s : X)⁻¹) * (y * t * y⁻¹ * (t : X)⁻¹) := by rw [← h1]; group)
  have hker : f.ker = (S ⊓ Subgroup.centralizer {y}).subgroupOf S := by
    ext s
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : y * (s : X) * y⁻¹ * (s : X)⁻¹ = 1 := congrArg Subtype.val h
      refine ⟨s.2, ?_⟩
      exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h')).symm
    · rintro ⟨-, h⟩
      apply Subtype.ext
      show y * (s : X) * y⁻¹ * (s : X)⁻¹ = 1
      rw [← h]
      group
  have hcard1 : Nat.card f.ker * Nat.card f.range = Nat.card S :=
    Subgroup.card_ker_mul_card_range f
  have hcard2 : Nat.card f.range ≤ Nat.card Z := Subgroup.card_le_card_group _
  have hcard3 : Nat.card f.ker = Nat.card (S ⊓ Subgroup.centralizer {y} : Subgroup X) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  calc Nat.card S = Nat.card f.ker * Nat.card f.range := hcard1.symm
    _ ≤ Nat.card f.ker * Nat.card Z := Nat.mul_le_mul_left _ hcard2
    _ = _ := by rw [hcard3]

end Abelian

theorem exists_chief_factor {X : Type} [Group X] [Finite X] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hperf : commutator X = ⊤) (V : Subgroup X) [V.Normal] (hV : IsPGroup q V)
    (hnc : ∃ g : X, ∃ v ∈ V, g * v ≠ v * g) :
    ∃ U : Subgroup X, ∃ _ : U.Normal, U ≤ V ∧
      (∀ u ∈ U, u ^ q = 1) ∧
      (∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center X) ∧
      (∀ N : Subgroup X, N.Normal → N ≤ U → N = U ∨ N ≤ Subgroup.center X) ∧
      quotKer U (U ⊓ Subgroup.center X) ≠ ⊤ := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hex : ∃ n : ℕ, ∃ N : Subgroup X, N.Normal ∧ N ≤ V ∧
      (∃ g : X, ∃ v ∈ N, g * v ≠ v * g) ∧ Nat.card N = n :=
    ⟨_, V, inferInstance, le_rfl, hnc, rfl⟩
  obtain ⟨U, hUn, hUV, hUnc, hUcard⟩ := Nat.find_spec hex
  have hmin : ∀ N : Subgroup X, N.Normal → N ≤ V → (∃ g : X, ∃ v ∈ N, g * v ≠ v * g) →
      Nat.card U ≤ Nat.card N := fun N hN hNV hNnc =>
    hUcard ▸ Nat.find_min' hex ⟨N, hN, hNV, hNnc, rfl⟩
  have hnotcent : ∀ N : Subgroup X, N.Normal → N ≤ U → ¬ N ≤ Subgroup.center X → N = U := by
    intro N hN hNU hNc
    refine Subgroup.eq_of_le_of_card_ge hNU (hmin N hN (hNU.trans hUV) ?_)
    by_contra hcon
    exact hNc fun v hv => Subgroup.mem_center_iff.mpr fun g => by
      by_contra hne
      exact hcon ⟨g, v, hv, hne⟩
  have hnoc : ¬ ∀ u ∈ U, ∀ g : X, g * u = u * g := by
    intro h
    obtain ⟨g, v, hv, hgv⟩ := hUnc
    exact hgv (h v hv g)
  have hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center X := by
    have hbot : U ≠ ⊥ := by
      intro h
      obtain ⟨g, v, hv, hgv⟩ := hUnc
      rw [h, Subgroup.mem_bot] at hv
      exact hgv (by rw [hv]; simp)
    have hlt := commutator_lt_of_isPGroup hq (hV.to_le hUV) hbot
    have hcN : ⁅U, U⁆ ≤ Subgroup.center X := by
      by_contra hcon
      exact hlt.ne (hnotcent ⁅U, U⁆ inferInstance hlt.le hcon)
    intro a ha b hb
    exact hcN (Subgroup.commutator_mem_commutator ha hb)
  have hcc : ∀ {c : X}, c ∈ Subgroup.center X → ∀ y : X, Commute c y :=
    fun hc y => (Subgroup.mem_center_iff.mp hc y).symm
  have hcent_comm : ∀ a ∈ U, ∀ b ∈ U,
      Commute (b * a * b⁻¹ * a⁻¹) a ∧ Commute (b * a * b⁻¹ * a⁻¹) b := fun a ha b hb =>
    ⟨hcc (hcomm b hb a ha) a, hcc (hcomm b hb a ha) b⟩
  have hpow_central : ∀ u ∈ U, u ^ q ∈ Subgroup.center X := by
    obtain ⟨P, hPn, hP⟩ := exists_pow_subgroup U (Subgroup.center X) q (by
      intro a ha b hb hap hbp
      rw [mul_pow_of_commute (hcent_comm a ha b hb).1 (hcent_comm a ha b hb).2]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (hcomm b hb a ha) _)
        (Subgroup.mul_mem _ hap hbp))
    have hPU : P ≤ U := fun u hu => ((hP u).1 hu).1
    have hPnc : ¬ P ≤ Subgroup.center X := by
      obtain ⟨g, u, hu, hgu⟩ := hUnc
      have hunc : u ∉ Subgroup.center X := fun h => hgu (Subgroup.mem_center_iff.mp h g)
      obtain ⟨m, hm⟩ := hV ⟨u, hUV hu⟩
      have hm' : u ^ q ^ m = 1 := congrArg Subtype.val hm
      obtain ⟨k, hk1, hk2⟩ := exists_pow_mem_of_pow_eq_one (Subgroup.center X) hunc hm'
      intro hle
      exact hk1 (hle ((hP _).2 ⟨U.pow_mem hu _, hk2⟩))
    intro u hu
    have hPeq := hnotcent P hPn hPU hPnc
    have : u ∈ P := hPeq ▸ hu
    exact ((hP u).1 this).2
  have hmul_q : ∀ a ∈ U, ∀ b ∈ U, (a * b) ^ q = a ^ q * b ^ q := by
    intro a ha b hb
    obtain ⟨h1, h2⟩ := hcent_comm a ha b hb
    have hcq : (b * a * b⁻¹ * a⁻¹) ^ q = 1 :=
      comm_pow_eq_one h1 (fun y => Subgroup.mem_center_iff.mp (hpow_central a ha) y)
    obtain ⟨t, ht⟩ := hq.dvd_choose_self (by norm_num : 2 ≠ 0)
      (lt_of_le_of_ne hq.two_le (Ne.symm hq2))
    rw [mul_pow_of_commute h1 h2, ht, pow_mul, hcq, one_pow, one_mul]
  obtain ⟨E, hEn, hE⟩ := exists_pow_subgroup U ⊥ q (by
    intro a ha b hb hap hbp
    rw [Subgroup.mem_bot] at hap hbp ⊢
    rw [hmul_q a ha b hb, hap, hbp, one_mul])
  have hEU : E ≤ U := fun u hu => ((hE u).1 hu).1
  have hEnc : ¬ E ≤ Subgroup.center X := by
    intro hEc
    refine hnoc (centralizes_of_quot hperf fun u hu g => hEc ((hE _).2 ⟨?_, ?_⟩))
    · exact U.mul_mem (U.inv_mem hu) ((inferInstance : U.Normal).conj_mem u hu g)
    · rw [Subgroup.mem_bot, hmul_q _ (U.inv_mem hu) _ ((inferInstance : U.Normal).conj_mem u hu g),
        inv_pow, conj_pow, Subgroup.mem_center_iff.mp (hpow_central u hu) g]
      group
  have hEeq := hnotcent E hEn hEU hEnc
  refine ⟨U, hUn, hUV, ?_, hcomm, fun N hN hNU => ?_, ?_⟩
  · intro u hu
    have : u ∈ E := hEeq ▸ hu
    exact Subgroup.mem_bot.mp ((hE u).1 this).2
  · by_cases hc : N ≤ Subgroup.center X
    · exact Or.inr hc
    · exact Or.inl (hnotcent N hN hNU hc)
  · intro htop
    refine hnoc (centralizes_of_quot hperf fun u hu g => ?_)
    have hg : g ∈ quotKer U (U ⊓ Subgroup.center X) := by rw [htop]; exact Subgroup.mem_top g
    exact (Subgroup.mem_inf.mp (mem_quotKer.mp hg u hu)).2

theorem card_le_of_abelian_le {X : Type} [Group X] [Finite X] {q : ℕ} (hq : q.Prime)
    (U : Subgroup X) (hexp : ∀ u ∈ U, u ^ q = 1)
    (hcl : ∀ a ∈ U, ∀ b ∈ U, ∀ c ∈ U, a * b * a⁻¹ * b⁻¹ * c = c * (a * b * a⁻¹ * b⁻¹))
    (hab : ∀ A : Subgroup X, A ≤ U → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A ≤ q ^ 3) :
    Nat.card U ≤ q ^ 4 * Nat.card (U ⊓ Subgroup.centralizer (U : Set X) : Subgroup X) ∧
      (Nat.card U = q ^ 4 * Nat.card (U ⊓ Subgroup.centralizer (U : Set X) : Subgroup X) →
        Nat.card (U ⊓ Subgroup.centralizer (U : Set X) : Subgroup X) = q) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  generalize hZdef : U ⊓ Subgroup.centralizer (U : Set X) = Z
  have hZU : Z ≤ U := hZdef ▸ inf_le_left
  have hZcen : ∀ z ∈ Z, ∀ u ∈ U, z * u = u * z := by
    intro z hz u hu
    rw [← hZdef] at hz
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 u hu).symm
  have hZcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Z := by
    intro a ha b hb
    rw [← hZdef]
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_iff.2 fun c hc =>
      (hcl a ha b hb c hc).symm⟩
    exact U.mul_mem (U.mul_mem (U.mul_mem ha hb) (U.inv_mem ha)) (U.inv_mem hb)
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hqpos : 0 < q := hq.pos
  by_cases habel : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a
  ·
    have hUZ : U ≤ Z := by
      intro u hu
      rw [← hZdef]
      exact Subgroup.mem_inf.2 ⟨hu, Subgroup.mem_centralizer_iff.2 fun h hh => habel h hh u hu⟩
    rw [le_antisymm hZU hUZ]
    have hpos : 0 < Nat.card U := Nat.card_pos
    refine ⟨Nat.le_mul_of_pos_left _ (pow_pos hqpos 4), fun h => ?_⟩
    have h1 : Nat.card U * 1 = Nat.card U * q ^ 4 := by rw [mul_one]; exact h.trans (mul_comm _ _)
    have h2 : 1 = q ^ 4 := Nat.eq_of_mul_eq_mul_left hpos h1
    have h3 : 1 < q ^ 4 := Nat.one_lt_pow (by norm_num) hq.one_lt
    omega
  · simp only [not_forall] at habel
    obtain ⟨x, hxU, u0, hu0, hxu⟩ := habel
    have hxZ : x ∉ Z := fun h => hxu (hZcen x h u0 hu0)
    have hqz : q ≤ Nat.card Z := by
      have hz0 := hZcomm x hxU u0 hu0
      have hz0ne : x * u0 * x⁻¹ * u0⁻¹ ≠ 1 := fun h =>
        hxu (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h))
      have hpow : (x * u0 * x⁻¹ * u0⁻¹) ^ q = 1 :=
        hexp _ (U.mul_mem (U.mul_mem (U.mul_mem hxU hu0) (U.inv_mem hxU)) (U.inv_mem hu0))
      have hord : orderOf (x * u0 * x⁻¹ * u0⁻¹) = q := by
        rcases (Nat.dvd_prime hq).1 (orderOf_dvd_of_pow_eq_one hpow) with h | h
        · exact absurd (orderOf_eq_one_iff.1 h) hz0ne
        · exact h
      have hdvd : q ∣ Nat.card Z := by
        rw [← hord]
        exact Subgroup.orderOf_dvd_natCard Z hz0
      exact Nat.le_of_dvd hZpos hdvd
    obtain ⟨B, hBU, hBab, hB5, hB1, hB2⟩ : ∃ B : Subgroup X, B ≤ U ∧
        (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
        (∀ w ∈ U, x * w = w * x → ∀ a ∈ B, a * w = w * a) ∧
        q * Nat.card Z ≤ Nat.card B ∧ Nat.card B ≤ q ^ 3 := by
      have hBU : Z ⊔ Subgroup.zpowers x ≤ U := sup_le hZU (Subgroup.zpowers_le.2 hxU)
      have hBab : ∀ a ∈ Z ⊔ Subgroup.zpowers x, ∀ b ∈ Z ⊔ Subgroup.zpowers x, a * b = b * a :=
        sup_comm_aux (fun a ha b hb => hZcen a ha b (hZU hb)) (zpowers_comm x)
          (zpowers_comm_of_commute fun a ha => hZcen a ha x hxU)
      refine ⟨Z ⊔ Subgroup.zpowers x, hBU, hBab, ?_, ?_, hab _ hBU hBab⟩
      · intro w hw hxw
        have hle : Z ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer {w} :=
          sup_le (fun z hz => Subgroup.mem_centralizer_singleton_iff.2 (hZcen z hz w hw))
            (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hxw))
        intro a ha
        exact Subgroup.mem_centralizer_singleton_iff.1 (hle ha)
      · refine q_mul_card_le hq hexp le_sup_left hBU fun h => hxZ ?_
        rw [h]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    by_cases hcase : ∃ y ∈ U, x * y = y * x ∧ y ∉ B
    · obtain ⟨y, hyU, hxy, hyB⟩ := hcase
      obtain ⟨A, hAU, hAab, hA5, hA1, hA2⟩ : ∃ A : Subgroup X, A ≤ U ∧
          (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
          (∀ w ∈ U, x * w = w * x → y * w = w * y → ∀ a ∈ A, a * w = w * a) ∧
          Nat.card A ≤ q ^ 3 ∧ q * Nat.card B ≤ Nat.card A := by
        have hBy : ∀ a ∈ B, a * y = y * a := hB5 y hyU hxy
        have hAU : B ⊔ Subgroup.zpowers y ≤ U := sup_le hBU (Subgroup.zpowers_le.2 hyU)
        have hAab : ∀ a ∈ B ⊔ Subgroup.zpowers y, ∀ b ∈ B ⊔ Subgroup.zpowers y, a * b = b * a :=
          sup_comm_aux hBab (zpowers_comm y) (zpowers_comm_of_commute hBy)
        refine ⟨B ⊔ Subgroup.zpowers y, hAU, hAab, ?_, hab _ hAU hAab, ?_⟩
        · intro w hw hxw hyw
          have hle : B ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer {w} :=
            sup_le (fun b hb => Subgroup.mem_centralizer_singleton_iff.2 (hB5 w hw hxw b hb))
              (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hyw))
          intro a ha
          exact Subgroup.mem_centralizer_singleton_iff.1 (hle ha)
        · refine q_mul_card_le hq hexp le_sup_left hAU fun h => hyB ?_
          rw [h]
          exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
      have hzq : Nat.card Z = q := by
        have h1 : q * q * Nat.card Z ≤ q * q * q := by
          calc q * q * Nat.card Z = q * (q * Nat.card Z) := by ring
            _ ≤ q * Nat.card B := Nat.mul_le_mul_left _ hB1
            _ ≤ Nat.card A := hA2
            _ ≤ q ^ 3 := hA1
            _ = q * q * q := by ring
        exact le_antisymm (Nat.le_of_mul_le_mul_left h1 (Nat.mul_pos hqpos hqpos)) hqz
      have hAcard : q ^ 3 ≤ Nat.card A := by
        calc q ^ 3 = q * (q * q) := by ring
          _ ≤ q * (q * Nat.card Z) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hqz)
          _ ≤ q * Nat.card B := Nat.mul_le_mul_left _ hB1
          _ ≤ Nat.card A := hA2
      have hmax : ∀ w ∈ U, x * w = w * x → y * w = w * y → w ∈ A := fun w hw hxw hyw =>
        mem_of_commute_of_card hab hAU hAab hAcard hw (hA5 w hw hxw hyw)
      have h1 := card_le_inf_centralizer_mul hcl hZcomm (le_refl U) hxU
      have h2 := card_le_inf_centralizer_mul hcl hZcomm
        (inf_le_left : U ⊓ Subgroup.centralizer {x} ≤ U) hyU
      have h3 : Nat.card ((U ⊓ Subgroup.centralizer {x}) ⊓ Subgroup.centralizer {y} :
          Subgroup X) ≤ q ^ 3 := by
        refine le_trans (Subgroup.card_le_of_le ?_) hA1
        intro w hw
        obtain ⟨hw1, hwy⟩ := Subgroup.mem_inf.1 hw
        obtain ⟨hwU, hwx⟩ := Subgroup.mem_inf.1 hw1
        exact hmax w hwU (Subgroup.mem_centralizer_singleton_iff.1 hwx).symm
          (Subgroup.mem_centralizer_singleton_iff.1 hwy).symm
      refine ⟨?_, fun _ => hzq⟩
      calc Nat.card U
          ≤ Nat.card (U ⊓ Subgroup.centralizer {x} : Subgroup X) * Nat.card Z := h1
        _ ≤ (Nat.card ((U ⊓ Subgroup.centralizer {x}) ⊓ Subgroup.centralizer {y} : Subgroup X) *
            Nat.card Z) * Nat.card Z := Nat.mul_le_mul_right _ h2
        _ ≤ (q ^ 3 * Nat.card Z) * Nat.card Z :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h3)
        _ = q ^ 4 * Nat.card Z := by rw [hzq]; ring
    · have hcase' : ∀ y ∈ U, x * y = y * x → y ∈ B := fun y hy hxy =>
        by_contra fun hyB => hcase ⟨y, hy, hxy, hyB⟩
      have h1 := card_le_inf_centralizer_mul hcl hZcomm (le_refl U) hxU
      have h2 : Nat.card (U ⊓ Subgroup.centralizer {x} : Subgroup X) ≤ q ^ 3 := by
        refine le_trans (Subgroup.card_le_of_le ?_) hB2
        intro y hy
        obtain ⟨hyU, hyc⟩ := Subgroup.mem_inf.1 hy
        exact hcase' y hyU (Subgroup.mem_centralizer_singleton_iff.1 hyc).symm
      have h3 : Nat.card U < q ^ 4 * Nat.card Z :=
        calc Nat.card U
            ≤ Nat.card (U ⊓ Subgroup.centralizer {x} : Subgroup X) * Nat.card Z := h1
          _ ≤ q ^ 3 * Nat.card Z := Nat.mul_le_mul_right _ h2
          _ < q ^ 4 * Nat.card Z :=
            Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right hq.one_lt (by norm_num)) hZpos
      exact ⟨h3.le, fun h => absurd h h3.ne⟩

end CFSG.LocalAnalysis.GLTheoremA.H248L227
