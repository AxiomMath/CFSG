module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSetup

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section InnerPart

variable {Γ : Type} [Group Γ]

def innerPart (J B : Subgroup Γ) : Subgroup Γ where
  carrier := {b | b ∈ B ∧ InnerOn J b}
  mul_mem' := by
    rintro b₁ b₂ ⟨hb₁, a₁, ha₁, h₁⟩ ⟨hb₂, a₂, ha₂, h₂⟩
    refine ⟨B.mul_mem hb₁ hb₂, a₁ * a₂, J.mul_mem ha₁ ha₂, fun j hj => ?_⟩
    have hj' : a₂ * j * a₂⁻¹ ∈ J := J.mul_mem (J.mul_mem ha₂ hj) (J.inv_mem ha₂)
    calc b₁ * b₂ * j * (b₁ * b₂)⁻¹ = b₁ * (b₂ * j * b₂⁻¹) * b₁⁻¹ := by group
      _ = b₁ * (a₂ * j * a₂⁻¹) * b₁⁻¹ := by rw [h₂ j hj]
      _ = a₁ * (a₂ * j * a₂⁻¹) * a₁⁻¹ := h₁ _ hj'
      _ = a₁ * a₂ * j * (a₁ * a₂)⁻¹ := by group
  one_mem' := ⟨B.one_mem, 1, J.one_mem, fun j _ => by simp⟩
  inv_mem' := by
    rintro b ⟨hb, a, ha, h⟩
    refine ⟨B.inv_mem hb, a⁻¹, J.inv_mem ha, fun j hj => ?_⟩
    have hj' : a⁻¹ * j * a ∈ J := J.mul_mem (J.mul_mem (J.inv_mem ha) hj) ha
    have h1 := h _ hj'
    have h2 : b * (a⁻¹ * j * a) * b⁻¹ = j := by rw [h1]; group
    calc b⁻¹ * j * b⁻¹⁻¹ = b⁻¹ * (b * (a⁻¹ * j * a) * b⁻¹) * b := by rw [h2]; group
      _ = a⁻¹ * j * a⁻¹⁻¹ := by group

theorem mem_innerPart {J B : Subgroup Γ} {b : Γ} : b ∈ innerPart J B ↔ b ∈ B ∧ InnerOn J b := Iff.rfl

theorem innerOn_of_mem_centralizer {J : Subgroup Γ} {b : Γ} (h : b ∈ Subgroup.centralizer (J : Set Γ)) :
    InnerOn J b :=
  ⟨1, J.one_mem, fun j hj => by
    have := Subgroup.mem_centralizer_iff.mp h j hj
    simp only [inv_one, mul_one, one_mul]
    rw [← this]; group⟩

theorem inf_centralizer_eq_of_act {J : Subgroup Γ} {x a : Γ} (h : ∀ j ∈ J, x * j * x⁻¹ = a * j * a⁻¹) :
    J ⊓ Subgroup.centralizer ({x} : Set Γ) = J ⊓ Subgroup.centralizer ({a} : Set Γ) := by
  ext j
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  refine and_congr_right fun hj => ?_
  have h1 := h j hj
  constructor
  · intro hjx
    have : x * j * x⁻¹ = j := by rw [← hjx]; group
    rw [this] at h1
    have : a * j * a⁻¹ = j := h1.symm
    calc j * a = a * j * a⁻¹ * a := by rw [this]
      _ = a * j := by group
  · intro hja
    have : a * j * a⁻¹ = j := by rw [← hja]; group
    rw [this] at h1
    calc j * x = x * j * x⁻¹ * x := by rw [h1]
      _ = x * j := by group

theorem eq_of_act_eq {J : Subgroup Γ} (hZ : Subgroup.center ↥J = ⊥) {a a' : Γ} (ha : a ∈ J) (ha' : a' ∈ J)
    (h : ∀ j ∈ J, a * j * a⁻¹ = a' * j * a'⁻¹) : a = a' := by
  have hc : (⟨a'⁻¹ * a, J.mul_mem (J.inv_mem ha') ha⟩ : ↥J) ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro j
    apply Subtype.ext
    show (j : Γ) * (a'⁻¹ * a) = a'⁻¹ * a * j
    have h1 := h j j.2
    calc (j : Γ) * (a'⁻¹ * a) = a'⁻¹ * (a' * j * a'⁻¹) * a := by group
      _ = a'⁻¹ * (a * j * a⁻¹) * a := by rw [← h1]
      _ = a'⁻¹ * a * j := by group
  rw [hZ] at hc
  have := congrArg Subtype.val (Subgroup.mem_bot.mp hc)
  simpa [inv_mul_eq_one, eq_comm] using this

theorem pow_eq_one_of_act {J : Subgroup Γ} (hZ : Subgroup.center ↥J = ⊥) {x a : Γ} {q : ℕ} (ha : a ∈ J)
    (h : ∀ j ∈ J, x * j * x⁻¹ = a * j * a⁻¹) (hxq : x ^ q = 1) : a ^ q = 1 := by
  have hpow : ∀ (n : ℕ) (j : Γ), j ∈ J → x ^ n * j * (x ^ n)⁻¹ = a ^ n * j * (a ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro j _; simp
    | succ n ih =>
      intro j hj
      have hj' : a * j * a⁻¹ ∈ J := J.mul_mem (J.mul_mem ha hj) (J.inv_mem ha)
      calc x ^ (n + 1) * j * (x ^ (n + 1))⁻¹ = x ^ n * (x * j * x⁻¹) * (x ^ n)⁻¹ := by group
        _ = x ^ n * (a * j * a⁻¹) * (x ^ n)⁻¹ := by rw [h j hj]
        _ = a ^ n * (a * j * a⁻¹) * (a ^ n)⁻¹ := ih _ hj'
        _ = a ^ (n + 1) * j * (a ^ (n + 1))⁻¹ := by group
  have h1 : ∀ j ∈ J, (1 : Γ) * j * (1 : Γ)⁻¹ = a ^ q * j * (a ^ q)⁻¹ := by
    intro j hj
    have := hpow q j hj
    rw [hxq] at this
    exact this
  exact (eq_of_act_eq hZ (J.pow_mem ha q) J.one_mem (fun j hj => (h1 j hj).symm)).trans rfl

theorem comm_of_act {J : Subgroup Γ} (hZ : Subgroup.center ↥J = ⊥) {x a g : Γ} (ha : a ∈ J)
    (h : ∀ j ∈ J, x * j * x⁻¹ = a * j * a⁻¹) (hg : g ∈ Subgroup.normalizer (J : Set Γ))
    (hgx : g * x = x * g) : g * a = a * g := by
  have hga : g * a * g⁻¹ ∈ J := by
    have := (Subgroup.mem_normalizer_iff.mp hg a).mp ha
    exact this
  have h2 : ∀ j ∈ J, (g * a * g⁻¹) * j * (g * a * g⁻¹)⁻¹ = a * j * a⁻¹ := by
    intro j hj
    have hj' : g⁻¹ * j * g ∈ J := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) j).mp hj
      simpa using this
    have h3 := h _ hj'
    have hxg : g * x * g⁻¹ = x := by rw [hgx]; group
    calc (g * a * g⁻¹) * j * (g * a * g⁻¹)⁻¹ = g * (a * (g⁻¹ * j * g) * a⁻¹) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * j * g) * x⁻¹) * g⁻¹ := by rw [h3]
      _ = (g * x * g⁻¹) * j * (g * x * g⁻¹)⁻¹ := by group
      _ = x * j * x⁻¹ := by rw [hxg]
      _ = a * j * a⁻¹ := h j hj
  have := eq_of_act_eq hZ hga ha h2
  calc g * a = g * a * g⁻¹ * g := by group
    _ = a * g := by rw [this]

end InnerPart

theorem exists_mem_not_mem_of_not_le {G : Type} [Group G] {B A M : Subgroup G} (hA : ¬ B ≤ A)
    (hM : ¬ B ≤ M) : ∃ g ∈ B, g ∉ A ∧ g ∉ M := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, haB, haA⟩ := SetLike.not_le_iff_exists.mp hA
  obtain ⟨m, hmB, hmM⟩ := SetLike.not_le_iff_exists.mp hM
  have haM : a ∈ M := hcon a haB haA
  have hmA : m ∈ A := by
    by_contra h
    exact hmM (hcon m hmB h)
  have hamA : a * m ∉ A := fun h => haA (by simpa using A.mul_mem h (A.inv_mem hmA))
  have hamM : a * m ∈ M := hcon _ (B.mul_mem haB hmB) hamA
  exact hmM (by simpa using M.mul_mem (M.inv_mem haM) hamM)

end CFSG.LocalAnalysis.GLTheoremA
