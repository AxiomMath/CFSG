module

public import Mathlib

public section

namespace CFSG.LieType.Chevalley

structure RootCombinatorics (W Φ ι : Type*) [Group W] [MulAction W Φ] where
  neg : Φ → Φ
  pos : Φ → Prop
  simple : ι → Φ
  refl : ι → W
  pos_or_pos_neg : ∀ α, pos α ∨ pos (neg α)
  not_pos_and_pos_neg : ∀ α, ¬(pos α ∧ pos (neg α))
  smul_neg : ∀ (w : W) α, w • neg α = neg (w • α)
  pos_simple : ∀ i, pos (simple i)
  refl_mul_self : ∀ i, refl i * refl i = 1
  refl_simple : ∀ i, refl i • simple i = neg (simple i)
  pos_refl : ∀ i α, pos α → α ≠ simple i → pos (refl i • α)

structure RootGroupData {W Φ ι : Type*} [Group W] [MulAction W Φ]
    (Rc : RootCombinatorics W Φ ι) (G : Type*) [Group G] where
  X : Φ → Subgroup G
  N : Subgroup G
  φ : N →* W
  n : ι → N
  φ_n : ∀ i, φ (n i) = Rc.refl i
  map_conj : ∀ (m : N) (α : Φ), (X α).map (MulAut.conj (m : G)).toMonoidHom = X (φ m • α)

namespace RootGroupData

variable {W Φ ι : Type*} [Group W] [MulAction W Φ] {Rc : RootCombinatorics W Φ ι}
variable {G : Type*} [Group G] (D : RootGroupData Rc G)

@[expose] def H : Subgroup G := D.φ.ker.map D.N.subtype

@[expose] def U : Subgroup G := ⨆ (α : Φ) (_ : Rc.pos α), D.X α

@[expose] def Ui (i : ι) : Subgroup G := ⨆ (α : Φ) (_ : Rc.pos α ∧ α ≠ Rc.simple i), D.X α

@[expose] def B : Subgroup G := D.H ⊔ D.U

variable {D}

theorem conj_mem (m : D.N) {α : Φ} {x : G} (hx : x ∈ D.X α) :
    (m : G) * x * (m : G)⁻¹ ∈ D.X (D.φ m • α) := by
  rw [← D.map_conj m α]
  exact ⟨x, hx, rfl⟩

theorem inv_conj_mem (m : D.N) {α : Φ} {x : G} (hx : x ∈ D.X α) :
    (m : G)⁻¹ * x * (m : G) ∈ D.X ((D.φ m)⁻¹ • α) := by
  have := conj_mem (D := D) m⁻¹ hx
  rwa [map_inv, Subgroup.coe_inv, inv_inv] at this

theorem mem_H_iff {g : G} : g ∈ D.H ↔ ∃ k : D.N, D.φ k = 1 ∧ (k : G) = g := by
  simp [H, MonoidHom.mem_ker]

theorem X_le_U {α : Φ} (hα : Rc.pos α) : D.X α ≤ D.U :=
  le_iSup₂_of_le α hα le_rfl

theorem Ui_le_U (i : ι) : D.Ui i ≤ D.U :=
  iSup₂_le fun _ hα => X_le_U hα.1

theorem X_le_Ui {i : ι} {α : Φ} (hα : Rc.pos α) (hne : α ≠ Rc.simple i) : D.X α ≤ D.Ui i :=
  le_iSup₂_of_le (f := fun (β : Φ) (_ : Rc.pos β ∧ β ≠ Rc.simple i) => D.X β) α ⟨hα, hne⟩ le_rfl

theorem H_le_B : D.H ≤ D.B := le_sup_left

theorem U_le_B : D.U ≤ D.B := le_sup_right

theorem le_normalizer_of_conj_mem {L K : Subgroup G}
    (h : ∀ g ∈ L, ∀ x ∈ K, g * x * g⁻¹ ∈ K) : L ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h g hg x hx, fun hx => ?_⟩
  have := h g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem conj_mem_of_iSup {S : Φ → Prop} {K : Subgroup G} (g : G)
    (h : ∀ α, S α → ∀ x ∈ D.X α, g * x * g⁻¹ ∈ K) {x : G}
    (hx : x ∈ ⨆ (α : Φ) (_ : S α), D.X α) : g * x * g⁻¹ ∈ K := by
  have hle : (⨆ (α : Φ) (_ : S α), D.X α) ≤ K.comap (MulAut.conj g).toMonoidHom :=
    iSup₂_le fun α hα y hy => h α hα y hy
  exact hle hx

theorem H_le_normalizer_U : D.H ≤ Subgroup.normalizer (D.U : Set G) := by
  refine le_normalizer_of_conj_mem fun g hg x hx => ?_
  obtain ⟨k, hk, rfl⟩ := mem_H_iff.mp hg
  refine conj_mem_of_iSup _ (fun α hα y hy => ?_) hx
  have := conj_mem k hy
  rw [hk, one_smul] at this
  exact X_le_U hα this

theorem simple_le_U (i : ι) : D.X (Rc.simple i) ≤ D.U := X_le_U (Rc.pos_simple i)

theorem U_eq_sup (i : ι) : D.U = D.Ui i ⊔ D.X (Rc.simple i) := by
  refine le_antisymm (iSup₂_le fun α hα => ?_) (sup_le (Ui_le_U i) (simple_le_U i))
  by_cases hαi : α = Rc.simple i
  · subst hαi
    exact le_sup_right
  · exact le_sup_of_le_left (le_iSup₂_of_le α ⟨hα, hαi⟩ le_rfl)

theorem simple_le_normalizer_Ui (i : ι)
    (hcomm : ∀ β, Rc.pos β → β ≠ Rc.simple i → ∀ x ∈ D.X (Rc.simple i), ∀ y ∈ D.X β,
      x * y * x⁻¹ * y⁻¹ ∈ D.Ui i) :
    D.X (Rc.simple i) ≤ Subgroup.normalizer (D.Ui i : Set G) := by
  refine le_normalizer_of_conj_mem fun x hx u hu => ?_
  refine conj_mem_of_iSup x (fun β hβ y hy => ?_) hu
  have h1 := hcomm β hβ.1 hβ.2 x hx y hy
  have h2 : y ∈ D.Ui i := X_le_Ui hβ.1 hβ.2 hy
  have := mul_mem h1 h2
  simpa [mul_assoc] using this

theorem conj_mem_Ui (i : ι) {x : G} (hx : x ∈ D.Ui i) :
    (D.n i : G) * x * (D.n i : G)⁻¹ ∈ D.Ui i := by
  refine conj_mem_of_iSup _ (fun α hα y hy => ?_) hx
  have hy' := conj_mem (D.n i) hy
  rw [D.φ_n] at hy'
  refine X_le_Ui (Rc.pos_refl i α hα.1 hα.2) (fun h => ?_) hy'
  have h' : α = Rc.refl i • Rc.simple i := by
    rw [← h, smul_smul, Rc.refl_mul_self, one_smul]
  rw [Rc.refl_simple] at h'
  exact Rc.not_pos_and_pos_neg _ ⟨Rc.pos_simple i, h' ▸ hα.1⟩

theorem inv_conj_mem_Ui (i : ι) {x : G} (hx : x ∈ D.Ui i) :
    (D.n i : G)⁻¹ * x * (D.n i : G) ∈ D.Ui i := by
  suffices h : (D.n i : G)⁻¹ * x * ((D.n i : G)⁻¹)⁻¹ ∈ D.Ui i by simpa using h
  refine conj_mem_of_iSup _ (fun α hα y hy => ?_) hx
  have hy' := inv_conj_mem (D.n i) hy
  rw [inv_inv]
  have hinv : (D.φ (D.n i))⁻¹ = Rc.refl i := by
    rw [D.φ_n, inv_eq_of_mul_eq_one_right (Rc.refl_mul_self i)]
  rw [hinv] at hy'
  refine X_le_Ui (Rc.pos_refl i α hα.1 hα.2) (fun h => ?_) hy'
  have h' : α = Rc.refl i • Rc.simple i := by
    rw [← h, smul_smul, Rc.refl_mul_self, one_smul]
  rw [Rc.refl_simple] at h'
  exact Rc.not_pos_and_pos_neg _ ⟨Rc.pos_simple i, h' ▸ hα.1⟩

theorem conj_mem_H (m : D.N) {h : G} (hh : h ∈ D.H) : (m : G) * h * (m : G)⁻¹ ∈ D.H := by
  obtain ⟨k, hk, rfl⟩ := mem_H_iff.mp hh
  exact mem_H_iff.mpr ⟨m * k * m⁻¹, by simp [hk], by simp⟩

theorem sq_mem_H (i : ι) : (D.n i : G) * (D.n i : G) ∈ D.H :=
  mem_H_iff.mpr ⟨D.n i * D.n i, by rw [map_mul, D.φ_n, Rc.refl_mul_self], rfl⟩

theorem exists_mul_of_mem_B {b : G} (hb : b ∈ D.B) : ∃ h ∈ D.H, ∃ u ∈ D.U, b = h * u := by
  have : (b : G) ∈ ((D.H ⊔ D.U : Subgroup G) : Set G) := hb
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ H_le_normalizer_U] at this
  obtain ⟨h, hh, u, hu, rfl⟩ := this
  exact ⟨h, hh, u, hu, rfl⟩

theorem exists_mul_of_mem_U (i : ι)
    (hnorm : D.X (Rc.simple i) ≤ Subgroup.normalizer (D.Ui i : Set G)) {u : G} (hu : u ∈ D.U) :
    ∃ v ∈ D.Ui i, ∃ x ∈ D.X (Rc.simple i), u = v * x := by
  have : (u : G) ∈ ((D.Ui i ⊔ D.X (Rc.simple i) : Subgroup G) : Set G) := by
    rw [← U_eq_sup]
    exact hu
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at this
  obtain ⟨v, hv, x, hx, rfl⟩ := this
  exact ⟨v, hv, x, hx, rfl⟩

theorem exists_simple_mul_eq (i : ι)
    (hnorm : D.X (Rc.simple i) ≤ Subgroup.normalizer (D.Ui i : Set G)) {b : G} (hb : b ∈ D.B) :
    ∃ b' ∈ D.B, ∃ x ∈ D.X (Rc.simple i), (D.n i : G) * b = b' * (D.n i : G) * x := by
  obtain ⟨h, hh, u, hu, rfl⟩ := exists_mul_of_mem_B hb
  obtain ⟨v, hv, x, hx, rfl⟩ := exists_mul_of_mem_U i hnorm hu
  refine ⟨((D.n i : G) * h * (D.n i : G)⁻¹) * ((D.n i : G) * v * (D.n i : G)⁻¹),
    mul_mem (H_le_B (conj_mem_H _ hh)) (U_le_B (Ui_le_U i (conj_mem_Ui i hv))), x, hx, ?_⟩
  group

theorem exists_simple_mul_of_pos (i : ι)
    (hnorm : D.X (Rc.simple i) ≤ Subgroup.normalizer (D.Ui i : Set G)) (m : D.N)
    (hm : Rc.pos ((D.φ m)⁻¹ • Rc.simple i)) {b : G} (hb : b ∈ D.B) :
    ∃ b₁ ∈ D.B, ∃ b₂ ∈ D.B, (D.n i : G) * b * m = b₁ * ((D.n i * m : D.N) : G) * b₂ := by
  obtain ⟨b', hb', x, hx, hbx⟩ := exists_simple_mul_eq i hnorm hb
  refine ⟨b', hb', (m : G)⁻¹ * x * m, U_le_B (X_le_U hm (inv_conj_mem m hx)), ?_⟩
  rw [hbx, Subgroup.coe_mul]
  group

variable (D) in
@[expose] def RankOne (i : ι) : Prop :=
  ∀ y ∈ D.X (Rc.neg (Rc.simple i)), y ∈ D.B ∨
    ∃ b₁ ∈ D.B, ∃ b₂ ∈ D.B, y = b₁ * (D.n i : G) * b₂

theorem exists_simple_mul (i : ι)
    (hnorm : D.X (Rc.simple i) ≤ Subgroup.normalizer (D.Ui i : Set G)) (hrank : D.RankOne i)
    (m : D.N) {b : G} (hb : b ∈ D.B) :
    (∃ b₁ ∈ D.B, ∃ b₂ ∈ D.B, (D.n i : G) * b * m = b₁ * ((D.n i * m : D.N) : G) * b₂) ∨
      ∃ b₁ ∈ D.B, ∃ b₂ ∈ D.B, (D.n i : G) * b * m = b₁ * (m : G) * b₂ := by
  by_cases hm : Rc.pos ((D.φ m)⁻¹ • Rc.simple i)
  · exact .inl (exists_simple_mul_of_pos i hnorm m hm hb)
  set m' : D.N := D.n i * m with hm'
  have hpos' : Rc.pos ((D.φ m')⁻¹ • Rc.simple i) := by
    have hneg := (Rc.pos_or_pos_neg ((D.φ m)⁻¹ • Rc.simple i)).resolve_left hm
    rw [hm', map_mul, mul_inv_rev, mul_smul, D.φ_n,
      inv_eq_of_mul_eq_one_right (Rc.refl_mul_self i), Rc.refl_simple, Rc.smul_neg]
    exact hneg
  obtain ⟨b', hb', x, hx, hbx⟩ := exists_simple_mul_eq i hnorm hb
  have hy : (D.n i : G) * x * (D.n i : G)⁻¹ ∈ D.X (Rc.neg (Rc.simple i)) := by
    have := conj_mem (D.n i) hx
    rwa [D.φ_n, Rc.refl_simple] at this
  have hrw : (D.n i : G) * b * m = b' * ((D.n i : G) * x * (D.n i : G)⁻¹) * (m' : G) := by
    rw [hbx, hm', Subgroup.coe_mul]
    group
  rcases hrank _ hy with hyB | ⟨c₁, hc₁, c₂, hc₂, hyc⟩
  · exact .inl ⟨b' * ((D.n i : G) * x * (D.n i : G)⁻¹), mul_mem hb' hyB, 1, one_mem _,
      by rw [hrw, mul_one]⟩
  · obtain ⟨d₁, hd₁, d₂, hd₂, hd⟩ := exists_simple_mul_of_pos i hnorm m' hpos' hc₂
    refine .inr ⟨b' * c₁ * d₁ * ((D.n i : G) * (D.n i : G)),
      mul_mem (mul_mem (mul_mem hb' hc₁) hd₁) (H_le_B (sq_mem_H i)), d₂, hd₂, ?_⟩
    rw [hrw, hyc]
    have : (D.n i : G) * c₂ * (m' : G) = d₁ * ((D.n i * m' : D.N) : G) * d₂ := hd
    calc b' * (c₁ * (D.n i : G) * c₂) * (m' : G)
        = b' * c₁ * ((D.n i : G) * c₂ * (m' : G)) := by group
      _ = b' * c₁ * (d₁ * ((D.n i * m' : D.N) : G) * d₂) := by rw [this]
      _ = b' * c₁ * d₁ * ((D.n i : G) * (D.n i : G)) * (m : G) * d₂ := by
        rw [hm', Subgroup.coe_mul, Subgroup.coe_mul]
        group

theorem exists_mem_doubleCoset
    (hnorm : ∀ i, D.X (Rc.simple i) ≤ Subgroup.normalizer (D.Ui i : Set G))
    (hrank : ∀ i, D.RankOne i)
    (hgen : Subgroup.closure ((D.B : Set G) ∪ Set.range fun i => (D.n i : G)) = ⊤) (g : G) :
    ∃ m : D.N, ∃ b₁ ∈ D.B, ∃ b₂ ∈ D.B, g = b₁ * (m : G) * b₂ := by
  have hB : ∀ b ∈ D.B, ∀ g : G, (∃ m : D.N, ∃ b₁ ∈ D.B, ∃ b₂ ∈ D.B, g = b₁ * (m : G) * b₂) →
      ∃ m : D.N, ∃ b₁ ∈ D.B, ∃ b₂ ∈ D.B, b * g = b₁ * (m : G) * b₂ := by
    rintro b hb g ⟨m, b₁, hb₁, b₂, hb₂, rfl⟩
    exact ⟨m, b * b₁, mul_mem hb hb₁, b₂, hb₂, by group⟩
  have hn : ∀ i, ∀ g : G, (∃ m : D.N, ∃ b₁ ∈ D.B, ∃ b₂ ∈ D.B, g = b₁ * (m : G) * b₂) →
      ∃ m : D.N, ∃ b₁ ∈ D.B, ∃ b₂ ∈ D.B, (D.n i : G) * g = b₁ * (m : G) * b₂ := by
    rintro i g ⟨m, b₁, hb₁, b₂, hb₂, rfl⟩
    rcases exists_simple_mul i (hnorm i) (hrank i) m hb₁ with
      ⟨c₁, hc₁, c₂, hc₂, hc⟩ | ⟨c₁, hc₁, c₂, hc₂, hc⟩
    · exact ⟨D.n i * m, c₁, hc₁, c₂ * b₂, mul_mem hc₂ hb₂, by
        rw [← mul_assoc, ← mul_assoc, hc]; group⟩
    · exact ⟨m, c₁, hc₁, c₂ * b₂, mul_mem hc₂ hb₂, by
        rw [← mul_assoc, ← mul_assoc, hc]; group⟩
  have hmem : g ∈ Subgroup.closure ((D.B : Set G) ∪ Set.range fun i => (D.n i : G)) := by
    rw [hgen]
    exact Subgroup.mem_top g
  induction hmem using Subgroup.closure_induction_left with
  | one => exact ⟨1, 1, one_mem _, 1, one_mem _, by simp⟩
  | mul_left x hx y _ ih =>
    rcases hx with hx | ⟨i, rfl⟩
    · exact hB x hx y ih
    · exact hn i y ih
  | inv_mul_cancel x hx y _ ih =>
    rcases hx with hx | ⟨i, rfl⟩
    · exact hB x⁻¹ (inv_mem hx) y ih
    ·
      have hsq : ((D.n i : G) * (D.n i : G))⁻¹ ∈ D.B := inv_mem (H_le_B (sq_mem_H i))
      obtain ⟨m, b₁, hb₁, b₂, hb₂, h⟩ := hn i _ (hB _ hsq y ih)
      refine ⟨m, b₁, hb₁, b₂, hb₂, ?_⟩
      rw [← h]
      group

theorem normalizer_le
    (hnorm : ∀ i, D.X (Rc.simple i) ≤ Subgroup.normalizer (D.Ui i : Set G))
    (hrank : ∀ i, D.RankOne i)
    (hgen : Subgroup.closure ((D.B : Set G) ∪ Set.range fun i => (D.n i : G)) = ⊤)
    (hdisj : ∀ α, ¬Rc.pos α → D.U ⊓ D.X α = ⊥) (hne : ∀ α, D.X α ≠ ⊥)
    (hW : ∀ w : W, (∀ i, Rc.pos (w • Rc.simple i)) → w = 1) :
    Subgroup.normalizer (D.U : Set G) ≤ D.B := by
  intro g hg
  obtain ⟨m, b₁, hb₁, b₂, hb₂, rfl⟩ := exists_mem_doubleCoset hnorm hrank hgen g
  have hBU : D.B ≤ Subgroup.normalizer (D.U : Set G) :=
    sup_le H_le_normalizer_U Subgroup.le_normalizer
  have hmN : (m : G) ∈ Subgroup.normalizer (D.U : Set G) := by
    have := mul_mem (mul_mem (inv_mem (hBU hb₁)) hg) (inv_mem (hBU hb₂))
    simpa [mul_assoc] using this
  have hφ : D.φ m = 1 := by
    refine hW _ fun i => ?_
    by_contra hneg
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (hne (Rc.simple i))
    have h1 : (m : G) * x * (m : G)⁻¹ ∈ D.U :=
      (Subgroup.mem_normalizer_iff.mp hmN x).mp (simple_le_U i x.2)
    have h3 : (m : G) * x * (m : G)⁻¹ ∈ D.U ⊓ D.X (D.φ m • Rc.simple i) :=
      ⟨h1, conj_mem m x.2⟩
    rw [hdisj _ hneg, Subgroup.mem_bot] at h3
    apply hx1
    have : (x : G) = 1 := by
      have := congrArg (fun z => (m : G)⁻¹ * z * m) h3
      simpa [mul_assoc] using this
    exact Subtype.ext this
  have hmH : (m : G) ∈ D.H := mem_H_iff.mpr ⟨m, hφ, rfl⟩
  exact mul_mem (mul_mem hb₁ (H_le_B hmH)) hb₂

theorem le_U_of_isPGroup (p : ℕ) (hH : Nat.Coprime (Nat.card D.H) p) {T : Subgroup G}
    (hT : IsPGroup p T) (hUT : D.U ≤ T) (hTB : T ≤ D.B) : T ≤ D.U := by
  intro t ht
  obtain ⟨h, hh, u, hu, rfl⟩ := exists_mul_of_mem_B (hTB ht)
  have hhT : h ∈ T := by
    have := mul_mem ht (inv_mem (hUT hu))
    simpa using this
  obtain ⟨k, hk⟩ := hT ⟨h, hhT⟩
  have hpow : h ^ p ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h2 : orderOf h ∣ p ^ k := orderOf_dvd_of_pow_eq_one hpow
  have h3 : orderOf h ∣ Nat.card D.H := by
    rw [← Subgroup.orderOf_mk h hh]
    exact orderOf_dvd_natCard _
  have hcop : Nat.gcd (p ^ k) (Nat.card D.H) = 1 := Nat.Coprime.pow_left k hH.symm
  have h1 : h = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h2 h3))
  rw [h1, one_mul]
  exact hu

theorem exists_sylow_eq_U [Finite G] (p : ℕ) [Fact p.Prime] (hU : IsPGroup p D.U)
    (hN : Subgroup.normalizer (D.U : Set G) ≤ D.B) (hH : Nat.Coprime (Nat.card D.H) p) :
    ∃ S : Sylow p G, (S : Subgroup G) = D.U := by
  obtain ⟨S, hS⟩ := hU.exists_le_sylow
  refine ⟨S, le_antisymm ?_ hS⟩
  have key : (S : Subgroup G) ⊓ Subgroup.normalizer (D.U : Set G) ≤ D.U :=
    le_U_of_isPGroup p hH (S.isPGroup'.to_le inf_le_left)
      (le_inf hS Subgroup.le_normalizer) (inf_le_right.trans hN)
  by_contra hne
  have : Group.IsNilpotent (S : Subgroup G) := S.isPGroup'.isNilpotent
  have hlt : D.U.subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne fun x hx => ?_
    have : (⟨x, hx⟩ : (S : Subgroup G)) ∈ D.U.subgroupOf S := htop ▸ Subgroup.mem_top _
    exact this
  obtain ⟨s, hsN, hsU⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hsU' : (s : G) ∉ D.U := hsU
  have hsNG : (s : G) ∈ Subgroup.normalizer (D.U : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact (Subgroup.mem_normalizer_iff.mp hsN ⟨x, hS hx⟩).mp hx
    · intro hx
      have hxS : x ∈ (S : Subgroup G) := by
        have := mul_mem (mul_mem (inv_mem s.2) (hS hx)) s.2
        simpa [mul_assoc] using this
      exact (Subgroup.mem_normalizer_iff.mp hsN ⟨x, hxS⟩).mpr hx
  exact hsU' (key ⟨s.2, hsNG⟩)

end RootGroupData

end CFSG.LieType.Chevalley
