module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Strong

open Subgroup CFSG.Open

open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem mem_conj_iff {g x : G} {H : Subgroup G} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem conj_mem_conj {g x : G} {H : Subgroup G} (hx : x ∈ H) :
    g * x * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom :=
  ⟨x, hx, rfl⟩

theorem map_conj_map_conj (a b : G) (H : Subgroup G) :
    (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem map_conj_le_of_forall {g : G} {H K : Subgroup G} (h : ∀ x ∈ H, g * x * g⁻¹ ∈ K) :
    H.map (MulAut.conj g).toMonoidHom ≤ K := by
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

theorem mem_normalizer_of_map_conj_eq {g : G} {H : Subgroup G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    rw [← h]
    exact conj_mem_conj hn
  · intro hn
    rw [← h, mem_conj_iff] at hn
    simpa [mul_assoc] using hn

theorem le_normalizer_of_weak (T : Sylow 2 G) {W : Subgroup G} (hWT : W ≤ T)
    (hweak : ∀ g : G, W.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      W.map (MulAut.conj g).toMonoidHom = W) :
    (T : Subgroup G) ≤ normalizer (W : Set G) := fun s hs =>
  mem_normalizer_of_map_conj_eq (hweak s (map_conj_le_of_forall fun _ hx =>
    mul_mem (mul_mem hs (hWT hx)) (inv_mem hs)))

theorem map_conj_inv_le_centralizer {W A B : Subgroup G} (hAW : A ≤ centralizer (W : Set G))
    {h : G} (hh : B.map (MulAut.conj h).toMonoidHom ≤ A) :
    W.map (MulAut.conj h⁻¹).toMonoidHom ≤ centralizer (B : Set G) := by
  rintro _ ⟨w, hw, rfl⟩
  rw [mem_centralizer_iff]
  intro b hb
  have hc : w * (h * b * h⁻¹) = h * b * h⁻¹ * w :=
    (mem_centralizer_iff.1 (hAW (hh (conj_mem_conj hb)))) w hw
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  calc b * (h⁻¹ * w * h) = h⁻¹ * (h * b * h⁻¹ * w) * h := by group
    _ = h⁻¹ * (w * (h * b * h⁻¹)) * h := by rw [hc]
    _ = h⁻¹ * w * h * b := by group

theorem elem_comm {A : Subgroup G} (hA : IsElemAbelian 2 A) {a b : G} (ha : a ∈ A)
    (hb : b ∈ A) : a * b = b * a :=
  isMulCommutative_iff_of_setLike.1 hA.1 a ha b hb

theorem elem_mul_self {A : Subgroup G} (hA : IsElemAbelian 2 A) {a : G} (ha : a ∈ A) :
    a * a = 1 := by
  rw [← pow_two]
  exact hA.2 a ha

theorem elem_map {A H : Subgroup G} (hA : IsElemAbelian 2 A) (hHA : H ≤ A) {G' : Type*}
    [Group G'] (f : G →* G') : IsElemAbelian 2 (H.map f) := by
  refine ⟨IsMulCommutative.of_setLike_mul_comm ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, elem_comm hA (hHA ha) (hHA hb)]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hA.2 a (hHA ha), map_one]

theorem eq_one_or_eq_of_mem_zpowers {t x : G} (ht : t * t = 1) (hx : x ∈ zpowers t) :
    x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht
  rw [zpow_eq_zpow_emod k h2]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem exists_twist {A : Subgroup G} (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {t : G}
    (htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A) :
    ∃ φ : A →* A, ∀ a : A, (φ a : G) = a * (t * a * t⁻¹) := by
  refine ⟨MonoidHom.mk' (fun a => a * ⟨t * a * t⁻¹, htA a a.2⟩) fun a b => ?_, fun a => rfl⟩
  apply Subtype.ext
  show (a : G) * b * (t * (a * b) * t⁻¹) = a * (t * a * t⁻¹) * (b * (t * b * t⁻¹))
  have hc := hcomm b b.2 _ (htA a a.2)
  calc (a : G) * b * (t * (a * b) * t⁻¹) = a * (b * (t * a * t⁻¹)) * (t * b * t⁻¹) := by group
    _ = a * ((t * a * t⁻¹) * b) * (t * b * t⁻¹) := by rw [hc]
    _ = a * (t * a * t⁻¹) * (b * (t * b * t⁻¹)) := by group

theorem commutator_zpowers_mul_le {A : Subgroup G} (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {x y : G} (hx : x ∈ A) (hy2 : y * y = 1) (hyN : y ∈ normalizer (A : Set G)) :
    ⁅A, zpowers (x * y)⁆ ≤ ⁅A, zpowers y⁆ := by
  rw [commutator_le]
  intro b hb z hz
  have hmul : (↑(A ⊔ zpowers y) : Set G) = A * zpowers y :=
    coe_mul_of_right_le_normalizer_left A (zpowers y) (zpowers_le.2 hyN)
  have hz' : z ∈ (A : Set G) * zpowers y := by
    rw [← hmul]
    exact (zpowers_le.2 (mul_mem_sup hx (mem_zpowers y))) hz
  obtain ⟨c, hc, w, hw, rfl⟩ := hz'
  show ⁅b, c * w⁆ ∈ ⁅A, zpowers y⁆
  rcases eq_one_or_eq_of_mem_zpowers hy2 hw with h | h <;> rw [h]
  · rw [mul_one, commutatorElement_def, hcomm b hb c hc, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  · have hu : y * b⁻¹ * y⁻¹ ∈ A := (mem_normalizer_iff.1 hyN b⁻¹).1 (inv_mem hb)
    have h1 : ⁅b, c * y⁆ = ⁅b, y⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc b * (c * y) * b⁻¹ * (c * y)⁻¹ = b * (c * (y * b⁻¹ * y⁻¹)) * c⁻¹ := by group
        _ = b * ((y * b⁻¹ * y⁻¹) * c) * c⁻¹ := by rw [hcomm c hc _ hu]
        _ = b * y * b⁻¹ * y⁻¹ := by group
    rw [h1]
    exact commutator_mem_commutator hb (mem_zpowers y)

theorem card_range_le_relIndex {H : Type*} [Group H] [Finite H] (φ : H →* H)
    (hKC : φ.range ≤ φ.ker) {B₁ : Subgroup H} (hB₁C : B₁ ≤ φ.ker) :
    Nat.card φ.range ≤ B₁.relIndex (B₁.comap φ) ∧
      Nat.card H ≤ Nat.card (B₁.comap φ) * B₁.relIndex (B₁.comap φ) := by
  have hCB₂ : φ.ker ≤ B₁.comap φ := fun x hx => by
    rw [MonoidHom.mem_ker] at hx
    rw [mem_comap, hx]
    exact one_mem _
  have hne : ∀ X Y : Subgroup H, X.relIndex Y ≠ 0 := fun X Y h => by
    have := Subgroup.relIndex_mul_card (H := X) (K := Y)
    rw [h, zero_mul] at this
    exact Nat.card_pos.ne' this.symm
  have h1 : (B₁.comap φ).index = B₁.relIndex φ.range := index_comap B₁ φ
  have h2 : B₁.relIndex φ.range ≤ B₁.relIndex φ.ker := relIndex_le_of_le_right hKC (hne _ _)
  have h3 : B₁.relIndex φ.ker * φ.ker.relIndex (B₁.comap φ) = B₁.relIndex (B₁.comap φ) :=
    relIndex_mul_relIndex _ _ _ hB₁C hCB₂
  have h4 : φ.ker.relIndex (B₁.comap φ) * (B₁.comap φ).index = φ.ker.index :=
    relIndex_mul_index hCB₂
  have h5 : φ.ker.index = Nat.card φ.range := index_ker φ
  have h6 : Nat.card (B₁.comap φ) * (B₁.comap φ).index = Nat.card H := card_mul_index _
  have h7 : B₁.relIndex φ.ker ≤ B₁.relIndex (B₁.comap φ) := relIndex_le_of_le_right hCB₂ (hne _ _)
  constructor
  · rw [← h5, ← h4, ← h3, h1, mul_comm]
    exact Nat.mul_le_mul_right _ h2
  · rw [← h6]
    exact Nat.mul_le_mul_left _ (h1 ▸ h2.trans h7)

variable [Finite G]

theorem exists_map_conj_le_sylow {p : ℕ} [Fact p.Prime] (T : Sylow p G) {P : Subgroup G}
    (hP : IsPGroup p P) : ∃ k : G, P.map (MulAut.conj k).toMonoidHom ≤ T := by
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq G Q T
  refine ⟨k, ?_⟩
  rw [← hk, Sylow.coe_subgroup_smul]
  exact Subgroup.map_mono hQ

theorem exists_conj_le_isPGroup {p : ℕ} [Fact p.Prime] (H : Subgroup G) {P Q : Subgroup G}
    (hP : IsPGroup p P) (hQ : IsPGroup p Q) (hPH : P ≤ H) (hQH : Q ≤ H) :
    ∃ c ∈ H, ∃ R : Subgroup G, IsPGroup p R ∧ P ≤ R ∧ Q.map (MulAut.conj c).toMonoidHom ≤ R := by
  obtain ⟨P₁, hP₁⟩ := (hP.comap_of_injective H.subtype H.subtype_injective).exists_le_sylow
  obtain ⟨Q₁, hQ₁⟩ := (hQ.comap_of_injective H.subtype H.subtype_injective).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H Q₁ P₁
  refine ⟨c, c.2, (P₁ : Subgroup H).map H.subtype, P₁.isPGroup'.map _, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hPH hx⟩, hP₁ hx, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : (⟨y, hQH hy⟩ : H) ∈ (Q₁ : Subgroup H) := hQ₁ hy
    have : MulAut.conj c • (⟨y, hQH hy⟩ : H) ∈ MulAut.conj c • (Q₁ : Subgroup H) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ hy'
    rw [← Sylow.coe_subgroup_smul, hc] at this
    exact ⟨_, this, rfl⟩

theorem cor4_centralizer_eq (T : Sylow 2 G) {W A : Subgroup G} (hWT : W ≤ T)
    (hweak : ∀ g : G, W.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      W.map (MulAut.conj g).toMonoidHom = W)
    (hAT : A ≤ T) (hAW : A ≤ centralizer (W : Set G))
    (hAN : ∀ n ∈ normalizer (W : Set G), ∀ a ∈ A, n * a * n⁻¹ ∈ A)
    {B : Subgroup G} (hBT : B ≤ T) (hBA : ∃ h : G, B.map (MulAut.conj h).toMonoidHom ≤ A) :
    B ⊓ centralizer (W : Set G) = B ⊓ A := by
  obtain ⟨h, hh⟩ := hBA
  refine le_antisymm (fun x hx => ⟨hx.1, ?_⟩) (inf_le_inf_left B hAW)
  have hh₁ : (B ⊓ centralizer (W : Set G)).map (MulAut.conj h).toMonoidHom ≤ A :=
    (map_mono inf_le_left).trans hh
  have hW2 : IsPGroup 2 W := T.isPGroup'.to_le hWT
  have hWC : W ≤ centralizer ((B ⊓ centralizer (W : Set G) : Subgroup G) : Set G) :=
    fun w hw => mem_centralizer_iff.2 fun b hb => ((mem_centralizer_iff.1 hb.2) w hw).symm
  obtain ⟨c, hc, R, hR, hWR, hW'R⟩ := exists_conj_le_isPGroup _ hW2 (hW2.map _) hWC
    (map_conj_inv_le_centralizer hAW hh₁)
  obtain ⟨k, hk⟩ := exists_map_conj_le_sylow T hR
  have e1 : W.map (MulAut.conj k).toMonoidHom = W := hweak k ((map_mono hWR).trans hk)
  have e2 : W.map (MulAut.conj (k * (c * h⁻¹))).toMonoidHom = W := by
    apply hweak
    rw [← map_conj_map_conj, ← map_conj_map_conj]
    exact (map_mono hW'R).trans hk
  have e3 : W.map (MulAut.conj (c * h⁻¹)).toMonoidHom = W :=
    Subgroup.map_injective (MulAut.conj k).injective (by rw [map_conj_map_conj, e2, e1])
  have hn : c * h⁻¹ ∈ normalizer (W : Set G) := mem_normalizer_of_map_conj_eq e3
  have hxA : h * x * h⁻¹ ∈ A := hh₁ (conj_mem_conj hx)
  have hcx : x * c = c * x := (mem_centralizer_iff.1 hc) x hx
  have hmem := hAN _ hn _ hxA
  have heq : c * h⁻¹ * (h * x * h⁻¹) * (c * h⁻¹)⁻¹ = x := by
    calc c * h⁻¹ * (h * x * h⁻¹) * (c * h⁻¹)⁻¹ = c * x * c⁻¹ := by group
      _ = x := by rw [← hcx]; group
  rwa [heq] at hmem

theorem cor4_exists_conj (T : Sylow 2 G) {W A : Subgroup G} (hWT : W ≤ T)
    (hweak : ∀ g : G, W.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      W.map (MulAut.conj g).toMonoidHom = W)
    (hAT : A ≤ T) (hAW : A ≤ centralizer (W : Set G))
    (hAN : ∀ n ∈ normalizer (W : Set G), ∀ a ∈ A, n * a * n⁻¹ ∈ A)
    {B : Subgroup G} (hBT : B ≤ T) (hBA : ∃ h : G, B.map (MulAut.conj h).toMonoidHom ≤ A) :
    ∃ g : G, B.map (MulAut.conj g).toMonoidHom ≤ A ∧
      (T ⊓ normalizer (B : Set G) : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ T := by
  obtain ⟨h, hh⟩ := hBA
  have hW2 : IsPGroup 2 W := T.isPGroup'.to_le hWT
  have hWh := map_conj_inv_le_centralizer hAW hh
  obtain ⟨n, hn, R, hR, hNR, hW1R⟩ := exists_conj_le_isPGroup (normalizer (B : Set G))
    (T.isPGroup'.to_le inf_le_left) (hW2.map _) inf_le_right
    (hWh.trans (centralizer_le_normalizer _))
  obtain ⟨g, hg⟩ := exists_map_conj_le_sylow T hR
  have e : W.map (MulAut.conj (g * (n * h⁻¹))).toMonoidHom = W := by
    apply hweak
    rw [← map_conj_map_conj, ← map_conj_map_conj]
    exact (map_mono hW1R).trans hg
  have hBN : B ≤ (T : Subgroup G) ⊓ normalizer (B : Set G) := le_inf hBT le_normalizer
  have hB'T : B.map (MulAut.conj g).toMonoidHom ≤ T := (map_mono (hBN.trans hNR)).trans hg
  have hB'A : ∃ h' : G,
      (B.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h').toMonoidHom ≤ A :=
    ⟨h * g⁻¹, by rw [map_conj_map_conj, inv_mul_cancel_right]; exact hh⟩
  have hB'W : B.map (MulAut.conj g).toMonoidHom ≤ centralizer (W : Set G) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_iff]
    intro w hw
    rw [← e] at hw
    obtain ⟨w₀, hw₀, rfl⟩ := hw
    have hb' : n⁻¹ * b * n ∈ B := (mem_normalizer_iff''.1 hn b).1 hb
    have hc : n⁻¹ * b * n * (h⁻¹ * w₀ * h) = h⁻¹ * w₀ * h * (n⁻¹ * b * n) := by
      have := (mem_centralizer_iff.1 (hWh ⟨w₀, hw₀, rfl⟩)) _ hb'
      simpa [MulAut.conj_apply] using this
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc _ = g * n * (h⁻¹ * w₀ * h * (n⁻¹ * b * n)) * n⁻¹ * g⁻¹ := by group
      _ = g * n * (n⁻¹ * b * n * (h⁻¹ * w₀ * h)) * n⁻¹ * g⁻¹ := by rw [hc]
      _ = _ := by group
  have hEq := cor4_centralizer_eq T hWT hweak hAT hAW hAN hB'T hB'A
  refine ⟨g, fun x hx => ?_, (map_mono hNR).trans hg⟩
  have hx' : x ∈ B.map (MulAut.conj g).toMonoidHom ⊓ centralizer (W : Set G) := ⟨hx, hB'W hx⟩
  rw [hEq] at hx'
  exact hx'.2

theorem cor4 (T : Sylow 2 G) {W A : Subgroup G} (hWT : W ≤ T)
    (hweak : ∀ g : G, W.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      W.map (MulAut.conj g).toMonoidHom = W)
    (hA : IsElemAbelian 2 A) (hAT : A ≤ T) (hAW : A ≤ centralizer (W : Set G))
    (hAN : ∀ n ∈ normalizer (W : Set G), ∀ a ∈ A, n * a * n⁻¹ ∈ A)
    {t : G} (htT : t ∈ (T : Subgroup G)) (ht2 : t * t = 1) (htA : t ∉ A)
    (hconj : ∃ g : G, g * t * g⁻¹ ∈ A) :
    ∃ B : Subgroup G, B ≤ T ∧ IsElemAbelian 2 B ∧
      (∃ h : G, B.map (MulAut.conj h).toMonoidHom ≤ A) ∧ ¬ B ≤ A ∧
      Nat.card (⁅A, zpowers t⁆ : Subgroup G) ≤ A.relIndex B ∧ Nat.card A ≤ Nat.card B * A.relIndex B := by
  have hTA : ∀ s ∈ (T : Subgroup G), ∀ a ∈ A, s * a * s⁻¹ ∈ A := fun s hs =>
    hAN s (le_normalizer_of_weak T hWT hweak hs)
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => elem_comm hA ha hb
  have hsq : ∀ a ∈ A, a * a = 1 := fun a ha => elem_mul_self hA ha
  have hainv : ∀ a ∈ A, a⁻¹ = a := fun a ha => inv_eq_of_mul_eq_one_right (hsq a ha)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  obtain ⟨g, hgS, hgmax⟩ := Set.exists_max_image {g : G | g * t * g⁻¹ ∈ A}
    (fun g => Nat.card (A ⊓ A.comap (MulAut.conj g).toMonoidHom : Subgroup G)) (Set.toFinite _)
    hconj
  have hgS' : g * t * g⁻¹ ∈ A := hgS
  set B₁ : Subgroup G := A ⊓ A.comap (MulAut.conj g).toMonoidHom
  have hmemB₁ : ∀ x : G, x ∈ B₁ ↔ x ∈ A ∧ g * x * g⁻¹ ∈ A := fun x => Iff.rfl
  have hB₁A : B₁ ≤ A := inf_le_left
  have hB₁t : ∀ x ∈ B₁, x * t = t * x := by
    intro x hx
    have hc := hcomm _ ((hmemB₁ x).1 hx).2 _ hgS'
    calc x * t = g⁻¹ * ((g * x * g⁻¹) * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * (g * x * g⁻¹)) * g := by rw [hc]
      _ = t * x := by group
  have hAB₁ : ¬ A ≤ B₁ := by
    intro hle
    have heq : A.map (MulAut.conj g).toMonoidHom = A :=
      eq_of_le_of_card_ge (map_conj_le_of_forall fun x hx => ((hmemB₁ x).1 (hle hx)).2)
        (card_map_of_injective (MulAut.conj g).injective).ge
    apply htA
    have hgt : g * t * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom := by rw [heq]; exact hgS'
    rw [mem_conj_iff] at hgt
    simpa [mul_assoc] using hgt
  obtain ⟨φ, hφ⟩ := exists_twist hcomm (hTA t htT)
  have hKC : φ.range ≤ φ.ker := by
    rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    have ha := hsq a a.2
    have ha' : ∀ x : G, (a : G) * (a * x) = x := fun x => by rw [← mul_assoc, ha, one_mul]
    have ht' : ∀ x : G, t * (t * x) = x := fun x => by rw [← mul_assoc, ht2, one_mul]
    rw [hφ, hφ, htinv]
    simp only [mul_assoc, ht2, ht', ha, ha', mul_one, OneMemClass.coe_one]
  have hB₁C : B₁.subgroupOf A ≤ φ.ker := by
    intro a ha
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    have hta : t * a * t⁻¹ = a := by
      rw [← hB₁t a (Subgroup.mem_subgroupOf.1 ha), mul_inv_cancel_right]
    rw [hφ, hta, OneMemClass.coe_one]
    exact hsq a a.2
  set B₂' : Subgroup A := (B₁.subgroupOf A).comap φ
  have hCB₂ : φ.ker ≤ B₂' := fun x hx => by
    rw [MonoidHom.mem_ker] at hx
    show φ x ∈ B₁.subgroupOf A
    rw [hx]
    exact one_mem _
  have hB₂B₁ : ¬ B₂' ≤ B₁.subgroupOf A := by
    intro hle
    apply hAB₁
    intro x hx
    exact hle (show (⟨x, hx⟩ : A) ∈ B₂' from hle (hCB₂ (hKC ⟨⟨x, hx⟩, rfl⟩)))
  set Q : Subgroup G := B₁ ⊔ zpowers t
  have hB₁Q : B₁ ≤ Q := le_sup_left
  have htQ : t ∈ Q := (le_sup_right : zpowers t ≤ Q) (mem_zpowers t)
  have hQT : Q ≤ T := sup_le (hB₁A.trans hAT) (zpowers_le.2 htT)
  have hQA : Q.map (MulAut.conj g).toMonoidHom ≤ A :=
    map_le_iff_le_comap.2 (sup_le inf_le_right (zpowers_le.2 hgS'))
  have hB₂A : B₂'.map A.subtype ≤ A := map_subtype_le _
  have hB₂N : B₂'.map A.subtype ≤ (T : Subgroup G) ⊓ normalizer (Q : Set G) := by
    refine le_inf (hB₂A.trans hAT) (le_normalizer_iff.2 ?_)
    rintro _ ⟨a, ha, rfl⟩ q hq
    have hφa : (a : G) * (t * a * t⁻¹) ∈ B₁ := by rw [← hφ]; exact ha
    have hQle : Q ≤ Q.comap (MulAut.conj (a : G)).toMonoidHom := by
      refine sup_le (fun b hb => ?_) (zpowers_le.2 ?_)
      · show (a : G) * b * (a : G)⁻¹ ∈ Q
        rw [hcomm a a.2 b (hB₁A hb), mul_inv_cancel_right]
        exact hB₁Q hb
      · show (a : G) * t * (a : G)⁻¹ ∈ Q
        have h1 : (a : G) * t * (a : G)⁻¹ = (a * (t * a * t⁻¹)) * t := by
          rw [hainv a a.2]
          group
        rw [h1]
        exact mul_mem (hB₁Q hφa) htQ
    exact hQle hq
  obtain ⟨g₁, hg₁A, hg₁T⟩ := cor4_exists_conj T hWT hweak hAT hAW hAN hQT ⟨g, hQA⟩
  have hg₁t : g₁ * t * g₁⁻¹ ∈ A := hg₁A (conj_mem_conj htQ)
  have hB₁eq : B₁ = A ⊓ A.comap (MulAut.conj g₁).toMonoidHom :=
    eq_of_le_of_card_ge (fun x hx => ⟨hB₁A hx, hg₁A (conj_mem_conj (hB₁Q hx))⟩) (hgmax g₁ hg₁t)
  have hmem₁ : ∀ x : G, x ∈ B₁ ↔ x ∈ A ∧ g₁ * x * g₁⁻¹ ∈ A := fun x => by rw [hB₁eq]; rfl
  have hB₁B₂ : B₁ ≤ B₂'.map A.subtype := fun x hx =>
    ⟨⟨x, hB₁A hx⟩, hCB₂ (hB₁C (x := ⟨x, hB₁A hx⟩) hx), rfl⟩
  have hinf : A ⊓ (B₂'.map A.subtype).map (MulAut.conj g₁).toMonoidHom =
      B₁.map (MulAut.conj g₁).toMonoidHom := by
    apply le_antisymm
    · rintro _ ⟨hyA, b, hb, rfl⟩
      exact ⟨b, (hmem₁ b).2 ⟨hB₂A hb, hyA⟩, rfl⟩
    · rintro _ ⟨b, hb, rfl⟩
      exact ⟨((hmem₁ b).1 hb).2, b, hB₁B₂ hb, rfl⟩
  have hrel : A.relIndex ((B₂'.map A.subtype).map (MulAut.conj g₁).toMonoidHom) =
      (B₁.subgroupOf A).relIndex B₂' := by
    calc A.relIndex ((B₂'.map A.subtype).map (MulAut.conj g₁).toMonoidHom)
        = (A ⊓ (B₂'.map A.subtype).map (MulAut.conj g₁).toMonoidHom).relIndex
            ((B₂'.map A.subtype).map (MulAut.conj g₁).toMonoidHom) :=
          (inf_relIndex_right _ _).symm
      _ = (B₁.map (MulAut.conj g₁).toMonoidHom).relIndex
            ((B₂'.map A.subtype).map (MulAut.conj g₁).toMonoidHom) := by rw [hinf]
      _ = B₁.relIndex (B₂'.map A.subtype) :=
          relIndex_map_map_of_injective _ _ (MulAut.conj g₁).injective
      _ = ((B₁.subgroupOf A).map A.subtype).relIndex (B₂'.map A.subtype) := by
          rw [map_subgroupOf_eq_of_le hB₁A]
      _ = (B₁.subgroupOf A).relIndex B₂' := relIndex_map_map_of_injective _ _ A.subtype_injective
  have hcommEq : (⁅A, zpowers t⁆ : Subgroup G) = φ.range.map A.subtype := by
    apply le_antisymm
    · rw [commutator_le]
      intro x hx y hy
      rcases eq_one_or_eq_of_mem_zpowers ht2 hy with rfl | rfl
      · rw [commutatorElement_one_right]
        exact one_mem _
      · refine ⟨φ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, ?_⟩
        show (φ ⟨x, hx⟩ : G) = ⁅x, y⁆
        rw [hφ, commutatorElement_def, hainv x hx]
        group
    · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      have h1 : A.subtype (φ a) = ⁅(a : G), t⁆ := by
        show (φ a : G) = _
        rw [hφ, commutatorElement_def, hainv a a.2]
        group
      rw [h1]
      exact commutator_mem_commutator a.2 (mem_zpowers t)
  obtain ⟨hc1, hc2⟩ := card_range_le_relIndex φ hKC hB₁C
  refine ⟨(B₂'.map A.subtype).map (MulAut.conj g₁).toMonoidHom, (map_mono hB₂N).trans hg₁T,
    elem_map hA hB₂A _, ⟨g₁⁻¹, ?_⟩, ?_, ?_, ?_⟩
  · rw [map_conj_map_conj, inv_mul_cancel]
    intro x hx
    rw [mem_conj_iff] at hx
    simpa using hB₂A hx
  · intro hle
    apply hB₂B₁
    intro a ha
    exact (hmem₁ a).2 ⟨a.2, hle ⟨a, ⟨a, ha, rfl⟩, rfl⟩⟩
  · rw [hrel, hcommEq, card_map_of_injective A.subtype_injective]
    exact hc1
  · rw [hrel, card_map_of_injective (MulAut.conj g₁).injective,
      card_map_of_injective A.subtype_injective]
    exact hc2

theorem stronglyClosed_of_rank (T : Sylow 2 G) {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAT : A ≤ T)
    (hweak : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      A.map (MulAut.conj g).toMonoidHom = A)
    (hP0 : ∀ B : Subgroup G, B ≤ T → IsElemAbelian 2 B → A.relIndex B ≤ 8)
    (hP1 : ∀ j ∈ (T : Subgroup G), j ∉ A → j * j = 1 → 4 ≤ Nat.card (⁅A, zpowers j⁆ : Subgroup G))
    (hP2 : ∀ F : Subgroup G, F ≤ T → A ≤ F → A.relIndex F = 4 → (∀ f ∈ F, f * f ∈ A) →
      ∃ j ∈ F, j ∉ A ∧ 16 ≤ Nat.card (⁅A, zpowers j⁆ : Subgroup G)) :
    ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (T : Subgroup G) → g⁻¹ * a * g ∈ A := by
  intro a ha g htT
  by_contra htA
  have hTN : (T : Subgroup G) ≤ normalizer (A : Set G) := le_normalizer_of_weak T hAT hweak
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => elem_comm hA ha hb
  have hAW : A ≤ centralizer (A : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun y hy => hcomm y hy x hx
  have hAN : ∀ n ∈ normalizer (A : Set G), ∀ b ∈ A, n * b * n⁻¹ ∈ A := fun n hn b hb =>
    (mem_normalizer_iff.1 hn b).1 hb
  have key : ∀ u ∈ (T : Subgroup G), u * u = 1 → u ∉ A → (∃ h : G, h * u * h⁻¹ ∈ A) →
      Nat.card (⁅A, zpowers u⁆ : Subgroup G) ≤ 8 := by
    intro u huT hu2 huA hconj
    obtain ⟨B, hBT, hBel, -, -, hcard, -⟩ := cor4 T hAT hweak hA hAT hAW hAN huT hu2 huA hconj
    exact hcard.trans (hP0 B hBT hBel)
  have ht2 : (g⁻¹ * a * g) * (g⁻¹ * a * g) = 1 := by
    calc (g⁻¹ * a * g) * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
      _ = 1 := by rw [elem_mul_self hA ha]; group
  have htc : ∃ h : G, h * (g⁻¹ * a * g) * h⁻¹ ∈ A := ⟨g, by simpa [mul_assoc] using ha⟩
  obtain ⟨B, hBT, hBel, ⟨h, hBA⟩, hBnA, hcard, -⟩ :=
    cor4 T hAT hweak hA hAT hAW hAN htT ht2 htA htc
  have hq1 : A.relIndex B ≠ 1 := fun h1 => hBnA (relIndex_eq_one.1 h1)
  obtain ⟨k, hk⟩ := (T.isPGroup'.to_le hBT).exists_card_eq
  obtain ⟨m, -, hqm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (hk ▸ relIndex_dvd_card (H := A) (K := B))
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · interval_cases m
    · exact hq1 (by rw [hqm, pow_zero])
    · have h4 := hP1 _ htT htA ht2
      rw [hqm, pow_one] at hcard
      omega
  obtain ⟨d, hd⟩ := (T.isPGroup'.to_le (inf_le_right.trans hBT : A ⊓ B ≤ T)).exists_card_eq
  have hBcard : Nat.card B = 2 ^ m * 2 ^ d := by
    rw [← hqm, ← hd]
    exact (relIndex_mul_card (H := A) (K := B)).symm
  obtain ⟨F', hF'card, hDF', hF'B⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (n := d + 2) (H := A ⊓ B) (L := B) (by rw [hd]; exact pow_dvd_pow 2 (by omega))
    (by rw [hBcard, ← pow_add]; exact pow_dvd_pow 2 (by omega)) inf_le_right
  have hF'T : F' ≤ T := hF'B.trans hBT
  have hAF' : A ⊓ F' = A ⊓ B := le_antisymm (inf_le_inf_left A hF'B) (le_inf inf_le_left hDF')
  have hrelF' : A.relIndex F' = 4 := by
    have h1 := relIndex_mul_card (H := A) (K := F')
    rw [hAF', hd, hF'card, pow_add] at h1
    have hpos : 0 < 2 ^ d := by positivity
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans (by ring))
  have hmul : (↑(A ⊔ F') : Set G) = A * F' :=
    coe_mul_of_right_le_normalizer_left A F' (hF'T.trans hTN)
  have hFT : A ⊔ F' ≤ T := sup_le hAT hF'T
  have hrelF : A.relIndex (A ⊔ F') = 4 := by
    haveI : (A.subgroupOf T).Normal := (normal_subgroupOf_iff_le_normalizer hAT).2 hTN
    have h1 := relIndex_sup_left (K := A.subgroupOf T) (H := F'.subgroupOf T)
    rw [← subgroupOf_sup hAT hF'T, relIndex_subgroupOf hFT, relIndex_subgroupOf hF'T] at h1
    rw [h1, hrelF']
  have hsqF : ∀ f ∈ A ⊔ F', f * f ∈ A := by
    intro f hf
    have hf' : f ∈ (A : Set G) * F' := by rw [← hmul]; exact hf
    obtain ⟨x, hx, y, hy, rfl⟩ := hf'
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (elem_mul_self hBel (hF'B hy))
    have hyx : y * x * y⁻¹ ∈ A := hAN y (hTN (hF'T hy)) x hx
    have h1 : x * y * (x * y) = x * (y * x * y⁻¹) := by rw [hyinv]; group
    rw [h1]
    exact mul_mem hx hyx
  obtain ⟨j, hjF, hjA, hj16⟩ := hP2 _ hFT le_sup_left hrelF hsqF
  have hj' : j ∈ (A : Set G) * F' := by rw [← hmul]; exact hjF
  obtain ⟨x, hx, y, hy, rfl⟩ := hj'
  beta_reduce at hjA hj16
  have hyA : y ∉ A := fun hyA => hjA (mul_mem hx hyA)
  have hy2 : y * y = 1 := elem_mul_self hBel (hF'B hy)
  have h8 := key y (hF'T hy) hy2 hyA ⟨h, hBA (conj_mem_conj (hF'B hy))⟩
  have hle := Subgroup.card_le_of_le (commutator_zpowers_mul_le hcomm hx hy2 (hTN (hF'T hy)))
  omega

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Strong
