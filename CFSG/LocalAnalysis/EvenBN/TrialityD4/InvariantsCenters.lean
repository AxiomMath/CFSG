module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Invariants

public section

open Subgroup
open scoped commutatorElement

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem comm_D_F (b : d.Γ₀) (c e : d.Γ) (f g : d.Γ₀) (c' e' : d.Γ) (f' g' : d.Γ₀) :
    ⁅d.x₂ b * d.x₃ c * (d.x₄ e * d.x₅ f * d.x₆ g), d.x₃ c' * (d.x₄ e' * d.x₅ f' * d.x₆ g')⁆ =
      d.x₆ (d.tr (c' * e) + (d.tr (c * e') + b * f')) := by
  have hw : d.x₄ e * d.x₅ f * d.x₆ g ∈ d.W :=
    mul_mem (mul_mem (d.x₄_mem_W e) (d.x₅_mem_W f)) (d.x₆_mem_W g)
  have hs : d.x₂ b * d.x₃ c * (d.x₄ e * d.x₅ f * d.x₆ g) ∈ d.D :=
    mul_mem (mul_mem (d.x₂_mem_D b) (d.F_le_D (d.x₃_mem_F c))) (d.F_le_D (d.W_le_F hw))
  have h1 : ⁅d.x₂ b * d.x₃ c * (d.x₄ e * d.x₅ f * d.x₆ g), d.x₃ c'⁆ = d.x₆ (d.tr (c' * e)) := by
    have hy : d.x₅ f * d.x₆ g ∈ d.Y := mul_mem (d.x₅_mem_Y f) (d.x₆_mem_Y g)
    have hwc : ⁅d.x₄ e * d.x₅ f * d.x₆ g, d.x₃ c'⁆ = d.x₆ (d.tr (c' * e)) := by
      rw [← commutatorElement_inv, mul_assoc, commutatorElement_mul_right_conj, d.comm₃₄,
        d.comm_eq_one_of_M_Y (d.F_le_M (d.x₃_mem_F c')) hy, mul_one, mul_inv_cancel, mul_one,
        d.x₆_inv]
    have h23 : ⁅d.x₂ b * d.x₃ c, d.x₃ c'⁆ = 1 := by
      rw [commutatorElement_mul_left_eq_conj_mul,
        commutatorElement_eq_one_iff_commute.2 (commute_of_add d.x₃_add c c'),
        commutatorElement_eq_one_iff_commute.2 (d.commute₂₃ b c')]
      group
    rw [commutatorElement_mul_left_eq_conj_mul, hwc, h23, mul_one,
      mul_mul_inv_eq_of_commute ((mem_centralizer_iff.1 (d.S_le_centralizer_V
        (mul_mem (d.U₂_le_S (d.x₂_mem_U₂ b)) (d.U₃_le_S (d.x₃_mem_U₃ c)))) _ (d.x₆_mem_V _)).symm)]
  have hV : ⁅d.x₂ b * d.x₃ c * (d.x₄ e * d.x₅ f * d.x₆ g),
      d.x₄ e' * d.x₅ f' * d.x₆ g'⁆ ∈ d.V := by
    rw [d.comm_D_W b c hw e' f' g']
    exact d.x₆_mem_V _
  rw [commutatorElement_mul_right_conj, h1, mul_mul_inv_eq_of_commute
    ((mem_centralizer_iff.1 (d.S_le_centralizer_V (d.U₃_le_S (d.x₃_mem_U₃ c'))) _ hV).symm),
    d.comm_D_W b c hw e' f' g', d.x₆_add, d.x₆_add, d.x₆_add]

theorem comm_x₂_W (b : d.Γ₀) (e : d.Γ) (f g : d.Γ₀) :
    ⁅d.x₂ b, d.x₄ e * d.x₅ f * d.x₆ g⁆ = d.x₆ (b * f) := by
  have h25 : ⁅d.x₂ b, d.x₅ f * d.x₆ g⁆ = d.x₆ (b * f) := by
    rw [commutatorElement_mul_right_conj, d.comm₂₅,
      commutatorElement_eq_one_iff_commute.2 (d.commute₂₆ b g), mul_one, mul_inv_cancel, mul_one]
  rw [mul_assoc, commutatorElement_mul_right_conj, h25,
    commutatorElement_eq_one_iff_commute.2 (d.commute₂₄ b e), one_mul,
    mul_mul_inv_eq_of_commute (d.commute₄₆ e _)]

theorem comm_D_D_formula (b : d.Γ₀) (c e : d.Γ) (f g b' : d.Γ₀) (c' e' : d.Γ) (f' g' : d.Γ₀) :
    ⁅d.x₂ b * d.x₃ c * (d.x₄ e * d.x₅ f * d.x₆ g),
      d.x₂ b' * d.x₃ c' * (d.x₄ e' * d.x₅ f' * d.x₆ g')⁆ =
      d.x₆ (b' * f + (d.tr (c' * e) + (d.tr (c * e') + b * f'))) := by
  have hw : d.x₄ e * d.x₅ f * d.x₆ g ∈ d.W :=
    mul_mem (mul_mem (d.x₄_mem_W e) (d.x₅_mem_W f)) (d.x₆_mem_W g)
  have h2 : ⁅d.x₂ b * d.x₃ c * (d.x₄ e * d.x₅ f * d.x₆ g), d.x₂ b'⁆ = d.x₆ (b' * f) := by
    have hwc : ⁅d.x₄ e * d.x₅ f * d.x₆ g, d.x₂ b'⁆ = d.x₆ (b' * f) := by
      rw [← commutatorElement_inv, d.comm_x₂_W, d.x₆_inv]
    have h23 : ⁅d.x₂ b * d.x₃ c, d.x₂ b'⁆ = 1 := by
      rw [commutatorElement_mul_left_eq_conj_mul,
        commutatorElement_eq_one_iff_commute.2 (d.commute₂₃ b' c).symm,
        commutatorElement_eq_one_iff_commute.2 (commute_of_add d.x₂_add b b')]
      group
    rw [commutatorElement_mul_left_eq_conj_mul, hwc, h23, mul_one,
      mul_mul_inv_eq_of_commute ((mem_centralizer_iff.1 (d.S_le_centralizer_V
        (mul_mem (d.U₂_le_S (d.x₂_mem_U₂ b)) (d.U₃_le_S (d.x₃_mem_U₃ c)))) _ (d.x₆_mem_V _)).symm)]
  have hV : ⁅d.x₂ b * d.x₃ c * (d.x₄ e * d.x₅ f * d.x₆ g),
      d.x₃ c' * (d.x₄ e' * d.x₅ f' * d.x₆ g')⁆ ∈ d.V := by
    rw [d.comm_D_F]
    exact d.x₆_mem_V _
  rw [mul_assoc (d.x₂ b'), commutatorElement_mul_right_conj, h2, mul_mul_inv_eq_of_commute
    ((mem_centralizer_iff.1 (d.S_le_centralizer_V (d.U₂_le_S (d.x₂_mem_U₂ b'))) _ hV).symm),
    d.comm_D_F, ← d.x₆_add]

theorem eq_nf_of_mem_S {s : X} (hs : s ∈ d.S) : s = d.x₁ (d.nfc s).1 *
    (d.x₂ (d.nfc s).2.1 * d.x₃ (d.nfc s).2.2.1 *
      (d.x₄ (d.nfc s).2.2.2.1 * d.x₅ (d.nfc s).2.2.2.2.1 * d.x₆ (d.nfc s).2.2.2.2.2)) := by
  conv_lhs => rw [← d.nf_nfc hs]
  rw [nf_apply]
  group

theorem comm_S_W {s : X} (hs : s ∈ d.S) (e : d.Γ) (f g : d.Γ₀) :
    ⁅s, d.x₄ e * d.x₅ f * d.x₆ g⁆ = d.x₆ (d.tr ((d.nfc s).2.2.1 * e) + (d.nfc s).2.1 * f) *
      d.x₅ (d.tr ((d.nfc s).1 * e)) := by
  have hn : d.x₄ (d.nfc s).2.2.2.1 * d.x₅ (d.nfc s).2.2.2.2.1 * d.x₆ (d.nfc s).2.2.2.2.2 ∈ d.W :=
    mul_mem (mul_mem (d.x₄_mem_W _) (d.x₅_mem_W _)) (d.x₆_mem_W _)
  have h1 : ⁅d.x₁ (d.nfc s).1, d.x₄ e * d.x₅ f * d.x₆ g⁆ = d.x₅ (d.tr ((d.nfc s).1 * e)) := by
    rw [mul_assoc, commutatorElement_mul_right_conj, d.comm₁₄,
      commutatorElement_mul_right_conj,
      commutatorElement_eq_one_iff_commute.2 (d.commute₁₅ _ f),
      commutatorElement_eq_one_iff_commute.2 (d.commute₁₆ _ g)]
    group
  conv_lhs => rw [d.eq_nf_of_mem_S hs]
  rw [commutatorElement_mul_left_eq_conj_mul, d.comm_D_W _ _ hn, h1,
    mul_mul_inv_eq_of_commute (d.commute₁₆ _ _)]

theorem x₆_mul_x₅_eq_one_iff {A B : d.Γ₀} : d.x₆ A * d.x₅ B = 1 ↔ A = 0 ∧ B = 0 := by
  constructor
  · intro h
    rw [← (d.commute₅₆ B A).eq] at h
    have h' : d.x₄ 0 * d.x₅ B * d.x₆ A = 1 := by rw [d.x₄_zero, one_mul, h]
    obtain ⟨-, hB, hA⟩ := d.eq_zero_of_x₄_x₅_x₆_eq_one h'
    exact ⟨hA, hB⟩
  · rintro ⟨rfl, rfl⟩
    rw [d.x₆_zero, d.x₅_zero, one_mul]

theorem mem_centralizer_W_iff {s : X} (hs : s ∈ d.S) (e : d.Γ) (f g : d.Γ₀) :
    s ∈ centralizer {d.x₄ e * d.x₅ f * d.x₆ g} ↔
      d.tr ((d.nfc s).1 * e) = 0 ∧ d.tr ((d.nfc s).2.2.1 * e) + (d.nfc s).2.1 * f = 0 := by
  rw [mem_centralizer_singleton_iff, ← commutatorElement_eq_one_iff_mul_comm,
    d.comm_S_W hs, d.x₆_mul_x₅_eq_one_iff, and_comm]

theorem card_Γ₀_submodule {V : Type*} [AddCommGroup V] [Module d.Γ₀ V] [Module.Finite d.Γ₀ V]
    (N : Submodule d.Γ₀ V) : Nat.card N = q ^ Module.finrank d.Γ₀ N := by
  rw [Module.natCard_eq_pow_finrank (K := d.Γ₀) (V := N), d.card_Γ₀]

theorem card_span_singleton_Γ₀ {V : Type*} [AddCommGroup V] [Module d.Γ₀ V] {v : V} (hv : v ≠ 0) :
    Nat.card (Submodule.span d.Γ₀ {v}) = q := by
  rw [← Nat.card_congr (LinearEquiv.toSpanNonzeroSingleton d.Γ₀ V v hv).toEquiv, d.card_Γ₀]

theorem x₄_x₅_x₆_mul (a a' : d.Γ) (b c b' c' : d.Γ₀) :
    d.x₄ a * d.x₅ b * d.x₆ c * (d.x₄ a' * d.x₅ b' * d.x₆ c') =
      d.x₄ (a + a') * d.x₅ (b + b') * d.x₆ (c + c') :=
  ((tripleHom d.x₄_add d.x₅_add d.x₆_add d.commute₄₅ d.commute₄₆ d.commute₅₆).map_mul
    (Multiplicative.ofAdd (a, b, c)) (Multiplicative.ofAdd (a', b', c'))).symm

theorem eq_nf_of_mem_W {w : X} (hw : w ∈ d.W) :
    w = d.x₄ (d.nfc w).2.2.2.1 * d.x₅ (d.nfc w).2.2.2.2.1 * d.x₆ (d.nfc w).2.2.2.2.2 ∧
      (d.nfc w).1 = 0 ∧ (d.nfc w).2.1 = 0 ∧ (d.nfc w).2.2.1 = 0 := by
  obtain ⟨a₄, a₅, a₆, rfl⟩ := d.mem_W_coords hw
  rw [nfc_nf]
  exact ⟨by simp only [nf_apply, d.x₁_zero, d.x₂_zero, d.x₃_zero, one_mul], rfl, rfl, rfl⟩

theorem nfc_W_mul {w w' : X} (hw : w ∈ d.W) (hw' : w' ∈ d.W) :
    (d.nfc (w * w')).2.2.2 = (d.nfc w).2.2.2 + (d.nfc w').2.2.2 := by
  obtain ⟨h, -⟩ := d.eq_nf_of_mem_W hw
  obtain ⟨h', -⟩ := d.eq_nf_of_mem_W hw'
  rw [h, h', d.x₄_x₅_x₆_mul, d.nfc_x₄_x₅_x₆, d.nfc_x₄_x₅_x₆, d.nfc_x₄_x₅_x₆]
  rfl

theorem exists_of_le_W {Z₀ T : Subgroup X} (hZW : Z₀ ≤ d.W) (hZ : q ^ 2 < Nat.card Z₀)
    (hTS : T ≤ d.S) (hTZ : ∀ t ∈ T, ∀ z ∈ Z₀, t * z = z * t) (hT : q ^ 8 < Nat.card T) :
    ∃ α : d.Γ, α ≠ 0 ∧ (∀ z ∈ Z₀, ∃ l : d.Γ₀, (d.nfc z).2.2.2.1 = l * α) ∧
      ∀ t ∈ T, (d.nfc t).2.1 = 0 ∧ d.tr ((d.nfc t).1 * α) = 0 ∧ d.tr ((d.nfc t).2.2.1 * α) = 0 := by
  classical
  have := d.finite
  have hq2 := d.two_le_q
  have hq1 : 1 < q := by omega
  let ψ : Z₀ →* Multiplicative (d.Γ₀ × d.Γ) :=
    { toFun := fun z => Multiplicative.ofAdd ((d.nfc z).2.2.2.2.1, (d.nfc z).2.2.2.1)
      map_one' := by
        change Multiplicative.ofAdd ((d.nfc 1).2.2.2.2.1, (d.nfc 1).2.2.2.1) = 1
        rw [d.nfc_one]
        rfl
      map_mul' := fun z z' => by
        change Multiplicative.ofAdd ((d.nfc ((z : X) * z')).2.2.2.2.1,
          (d.nfc ((z : X) * z')).2.2.2.1) = _
        have h := d.nfc_W_mul (hZW z.2) (hZW z'.2)
        simp only [Prod.ext_iff, Prod.snd_add, Prod.fst_add] at h
        rw [h.2.1, h.1]
        rfl }
  have hψ : ∀ z : Z₀, Multiplicative.toAdd (ψ z) = ((d.nfc z).2.2.2.2.1, (d.nfc z).2.2.2.1) :=
    fun _ => rfl
  set P := Subgroup.toAddSubgroup' ψ.range with hP
  have hmemP : ∀ p, p ∈ P ↔ ∃ z : Z₀, ((d.nfc z).2.2.2.2.1, (d.nfc z).2.2.2.1) = p := by
    intro p
    rw [Subgroup.mem_toAddSubgroup']
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, by rw [← hψ, hz, toAdd_ofAdd]⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, rfl⟩
  have hcardZ := card_eq_card_range_mul_card_ker ψ
  rw [← card_toAddSubgroup'_eq] at hcardZ
  have hker : Nat.card ψ.ker ≤ q := by
    calc Nat.card ψ.ker ≤ Nat.card d.Γ₀ := by
          refine Nat.card_le_card_of_injective (fun z => (d.nfc (z : X)).2.2.2.2.2)
            fun z z' h => ?_
          have hz := congrArg Multiplicative.toAdd (MonoidHom.mem_ker.1 z.2)
          have hz' := congrArg Multiplicative.toAdd (MonoidHom.mem_ker.1 z'.2)
          rw [hψ] at hz hz'
          simp only [toAdd_one, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at hz hz'
          obtain ⟨e1, -⟩ := d.eq_nf_of_mem_W (hZW z.1.2)
          obtain ⟨e2, -⟩ := d.eq_nf_of_mem_W (hZW z'.1.2)
          apply Subtype.ext; apply Subtype.ext
          rw [e1, e2, hz.1, hz.2, hz'.1, hz'.2]
          simp only at h
          rw [h]
      _ = q := d.card_Γ₀
  have hPq : q < Nat.card P := by
    by_contra h
    push Not at h
    have : Nat.card Z₀ ≤ q * q := by rw [hcardZ]; exact Nat.mul_le_mul h hker
    nlinarith
  set P₄ := P.map (AddMonoidHom.snd d.Γ₀ d.Γ) with hP₄
  have hcond : ∀ t : T, (∀ s ∈ P₄, d.trBilin s (d.nfc t).1 = 0) ∧
      ∀ s ∈ P, d.pairBilin s ((d.nfc t).2.1, (d.nfc t).2.2.1) = 0 := by
    intro t
    have key : ∀ z : Z₀, d.tr ((d.nfc t).1 * (d.nfc z).2.2.2.1) = 0 ∧
        d.tr ((d.nfc t).2.2.1 * (d.nfc z).2.2.2.1) + (d.nfc t).2.1 * (d.nfc z).2.2.2.2.1 = 0 := by
      intro z
      obtain ⟨e1, -⟩ := d.eq_nf_of_mem_W (hZW z.2)
      have h := hTZ t t.2 z z.2
      rw [← mem_centralizer_singleton_iff] at h
      rw [e1, d.mem_centralizer_W_iff (hTS t.2)] at h
      exact h
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · obtain ⟨p, hp, rfl⟩ := AddSubgroup.mem_map.1 hs
      obtain ⟨z, rfl⟩ := (hmemP p).1 hp
      rw [trBilin_apply]
      change d.tr ((d.nfc (z : X)).2.2.2.1 * (d.nfc (t : X)).1) = 0
      rw [mul_comm]
      exact (key z).1
    · obtain ⟨z, rfl⟩ := (hmemP s).1 hs
      rw [pairBilin_apply, mul_comm (d.nfc (z : X)).2.2.2.2.1, mul_comm (d.nfc (z : X)).2.2.2.1,
        add_comm]
      exact (key z).2
  let G : T → {a : d.Γ // ∀ s ∈ P₄, d.trBilin s a = 0} ×
      {z : d.Γ₀ × d.Γ // ∀ s ∈ P, d.pairBilin s z = 0} × d.Γ × d.Γ₀ × d.Γ₀ := fun t =>
    (⟨(d.nfc t).1, (hcond t).1⟩, ⟨((d.nfc t).2.1, (d.nfc t).2.2.1), (hcond t).2⟩,
      (d.nfc t).2.2.2.1, (d.nfc t).2.2.2.2.1, (d.nfc t).2.2.2.2.2)
  have hG : Function.Injective G := by
    intro t t' h
    simp only [G, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨h1, ⟨h2, h3⟩, h4, h5, h6⟩ := h
    apply Subtype.ext
    rw [← d.nf_nfc (hTS t.2), ← d.nf_nfc (hTS t'.2)]
    exact congrArg d.nf (Prod.ext h1 (Prod.ext h2 (Prod.ext h3 (Prod.ext h4 (Prod.ext h5 h6)))))
  have hTle := Nat.card_le_card_of_injective G hG
  simp only [Nat.card_prod, d.card_Γ, d.card_Γ₀] at hTle
  have hA₄ := card_span_mul_card_orth_eq d.trBilin d.trBilin_nondegenerate P₄
  have hA := card_span_mul_card_orth_eq d.pairBilin d.pairBilin_nondegenerate P
  rw [d.card_Γ] at hA₄
  rw [Nat.card_prod, d.card_Γ, d.card_Γ₀] at hA
  have hn₄ := d.card_Γ₀_submodule (Submodule.span d.Γ₀ (P₄ : Set d.Γ))
  have hn := d.card_Γ₀_submodule (Submodule.span d.Γ₀ (P : Set (d.Γ₀ × d.Γ)))
  set k₄ := Module.finrank d.Γ₀ (Submodule.span d.Γ₀ (P₄ : Set d.Γ)) with hk₄
  set k := Module.finrank d.Γ₀ (Submodule.span d.Γ₀ (P : Set (d.Γ₀ × d.Γ))) with hk
  set o₄ := Nat.card {a : d.Γ // ∀ s ∈ P₄, d.trBilin s a = 0} with ho₄
  set o := Nat.card {z : d.Γ₀ × d.Γ // ∀ s ∈ P, d.pairBilin s z = 0} with ho
  rw [hn₄] at hA₄
  rw [hn] at hA
  have hnP : Nat.card P ≤ q ^ k := by
    rw [← hn]
    exact Nat.card_le_card_of_injective (fun p => ⟨p, Submodule.subset_span p.2⟩)
      fun p p' h => Subtype.ext (congrArg Subtype.val h :)
  have hk2 : 2 ≤ k := by
    by_contra h
    push Not at h
    have : q ^ k ≤ q ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_one] at this
    omega
  have hsum : k₄ + k < 4 := by
    have h1 : Nat.card T * (q ^ k₄ * q ^ k) ≤ q ^ 12 := by
      calc Nat.card T * (q ^ k₄ * q ^ k) ≤ o₄ * (o * (q ^ 3 * (q * q))) * (q ^ k₄ * q ^ k) :=
            Nat.mul_le_mul_right _ hTle
        _ = (q ^ k₄ * o₄) * (q ^ k * o) * q ^ 5 := by ring
        _ = q ^ 12 := by rw [hA₄, hA]; ring
    have h2 : q ^ 8 * (q ^ k₄ * q ^ k) < q ^ 12 :=
      lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hT (by positivity)) h1
    rw [← pow_add, ← pow_add] at h2
    have := (Nat.pow_lt_pow_iff_right hq1).1 h2
    omega
  have hP₄ne : ∃ α ∈ P₄, α ≠ 0 := by
    by_contra h
    push Not at h
    have hZY : Z₀ ≤ d.Y := fun z hz => by
      obtain ⟨e1, -⟩ := d.eq_nf_of_mem_W (hZW hz)
      have h0 := h _ (AddSubgroup.mem_map_of_mem _ ((hmemP _).2 ⟨⟨z, hz⟩, rfl⟩))
      change (d.nfc z).2.2.2.1 = 0 at h0
      rw [e1, h0, d.x₄_zero, one_mul]
      exact mul_mem (d.x₅_mem_Y _) (d.x₆_mem_Y _)
    have := Subgroup.card_le_of_le hZY
    rw [d.card_Y] at this
    omega
  obtain ⟨α, hαP₄, hα0⟩ := hP₄ne
  have hαspan : Submodule.span d.Γ₀ {α} ≤ Submodule.span d.Γ₀ (P₄ : Set d.Γ) :=
    Submodule.span_le.2 (Set.singleton_subset_iff.2 (Submodule.subset_span hαP₄))
  have hk₄1 : 1 ≤ k₄ := by
    have := Submodule.finrank_mono hαspan
    rwa [finrank_span_singleton hα0] at this
  have hspan₄ : Submodule.span d.Γ₀ (P₄ : Set d.Γ) = Submodule.span d.Γ₀ {α} := by
    symm
    refine Submodule.eq_of_le_of_finrank_le hαspan ?_
    rw [finrank_span_singleton hα0]
    omega
  have hk2' : k = 2 := by omega
  have ho2 : o = q ^ 2 := by
    rw [hk2'] at hA
    have h : q ^ 2 * o = q ^ 2 * q ^ 2 := by rw [hA]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  set L := (Submodule.span d.Γ₀ {α}).toAddSubgroup with hL
  have hRcard : Nat.card {a : d.Γ // ∀ s ∈ L, d.trBilin s a = 0} = q ^ 2 := by
    have h1 := card_span_mul_card_orth_eq d.trBilin d.trBilin_nondegenerate L
    rw [d.card_Γ, show Submodule.span d.Γ₀ ((L : AddSubgroup d.Γ) : Set d.Γ) =
      Submodule.span d.Γ₀ {α} from Submodule.span_eq _, d.card_span_singleton_Γ₀ hα0] at h1
    have h : q * Nat.card {a : d.Γ // ∀ s ∈ L, d.trBilin s a = 0} = q * q ^ 2 := by
      rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) h
  set R : Set (d.Γ₀ × d.Γ) := {z | z.1 = 0 ∧ ∀ s ∈ L, d.trBilin s z.2 = 0} with hR
  have hRc : Nat.card R = q ^ 2 := by
    rw [← hRcard]
    refine Nat.card_congr ⟨fun z => ⟨z.1.2, z.2.2⟩, fun a => ⟨(0, a.1), rfl, a.2⟩,
      fun z => ?_, fun a => rfl⟩
    obtain ⟨⟨z1, z2⟩, hz1, hz2⟩ := z
    simp only at hz1
    subst hz1
    rfl
  have hRo : ∀ z ∈ R, ∀ s ∈ P, d.pairBilin s z = 0 := by
    rintro z ⟨hz1, hz2⟩ s hs
    have hs4 : s.2 ∈ L := by
      change s.2 ∈ Submodule.span d.Γ₀ {α}
      rw [← hspan₄]
      exact Submodule.subset_span (AddSubgroup.mem_map_of_mem _ hs)
    rw [pairBilin_apply, hz1, mul_zero, zero_add]
    exact hz2 _ hs4
  have horth : ∀ z : d.Γ₀ × d.Γ, (∀ s ∈ P, d.pairBilin s z = 0) → z ∈ R := by
    intro z hz
    by_contra hzR
    have hlt : R ⊂ {z | ∀ s ∈ P, d.pairBilin s z = 0} :=
      ⟨fun z hz => hRo z hz, fun h => hzR (h hz)⟩
    have := Set.ncard_lt_ncard hlt (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hRc] at this
    change q ^ 2 < o at this
    omega
  have hαL : α ∈ L := Submodule.subset_span (Set.mem_singleton α)
  refine ⟨α, hα0, fun z hz => ?_, fun t ht => ?_⟩
  · have hs4 : (d.nfc z).2.2.2.1 ∈ Submodule.span d.Γ₀ {α} := by
      rw [← hspan₄]
      exact Submodule.subset_span (AddSubgroup.mem_map_of_mem _ ((hmemP _).2 ⟨⟨z, hz⟩, rfl⟩))
    obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.1 hs4
    exact ⟨l, by rw [← hl, Algebra.smul_def]; rfl⟩
  · obtain ⟨h1, h2⟩ := horth _ (hcond ⟨t, ht⟩).2
    refine ⟨h1, ?_, ?_⟩
    · have := (hcond ⟨t, ht⟩).1 α hαP₄
      rwa [trBilin_apply, mul_comm] at this
    · have := h2 α hαL
      rwa [trBilin_apply, mul_comm] at this

theorem mem_F_of_mem_D_of_nfc_snd {g : X} (hg : g ∈ d.D) (h : (d.nfc g).2.1 = 0) : g ∈ d.F := by
  rw [d.eq_nf_of_mem_D hg, h, d.x₂_zero, one_mul]
  exact mul_mem (d.x₃_mem_F _) (mul_mem (mul_mem (d.x₄_mem_F _) (d.x₅_mem_F _)) (d.x₆_mem_F _))

theorem mem_M_of_mem_S_of_nfc_snd {g : X} (hg : g ∈ d.S) (h : (d.nfc g).2.1 = 0) : g ∈ d.M := by
  rw [d.eq_nf_of_mem_S hg, h, d.x₂_zero, one_mul]
  exact mul_mem (d.x₁_mem_M _) (d.F_le_M (mul_mem (d.x₃_mem_F _) (mul_mem (mul_mem
    (d.x₄_mem_F _) (d.x₅_mem_F _)) (d.x₆_mem_F _))))

theorem mul_eq_zero_of_comm₁₂_mem_W {a : d.Γ} {b : d.Γ₀} (h : ⁅d.x₁ a, d.x₂ b⁆ ∈ d.W) :
    a * b = 0 := by
  rw [d.comm₁₂, mul_assoc, mul_mem_cancel_right (mul_mem (d.x₄_mem_W _) (d.x₅_mem_W _)),
    d.x₃_mem_W_iff] at h
  exact h

theorem comm_x₂_mem_W_of_comm_mem_W {t n : X} {b : d.Γ₀} (ht : t ∈ d.S) (hn : n ∈ d.F)
    (h : ⁅t, d.x₂ b * n⁆ ∈ d.W) : ⁅t, d.x₂ b⁆ ∈ d.W := by
  rw [commutatorElement_mul_right_conj] at h
  exact (mul_mem_cancel_right ((mem_normalizer_iff.1 (d.S_le_normalizer_W
    (d.U₂_le_S (d.x₂_mem_U₂ b))) _).1 (d.commutator_S_F (commutator_mem_commutator ht hn)))).1 h

theorem nfc_fst_eq_zero_of_comm_x₂_mem_W {t : X} {b : d.Γ₀} (ht : t ∈ d.S) (hb : b ≠ 0)
    (h : ⁅t, d.x₂ b⁆ ∈ d.W) : (d.nfc t).1 = 0 := by
  obtain ⟨m, hm, htm⟩ := d.eq_x₁_mul_of_mem_S ht
  rw [htm, commutatorElement_mul_mem_iff (d.S_le_normalizer_W (d.U₁_le_S (d.x₁_mem_U₁ _)))
    (d.Y_le_W (d.V_le_Y (d.commutator_D_D (commutator_mem_commutator hm (d.x₂_mem_D b)))))] at h
  exact (mul_eq_zero.1 (d.mul_eq_zero_of_comm₁₂_mem_W h)).resolve_right
    (fun h0 => hb (Subtype.ext h0))

theorem nfc_fst_eq_zero_of_commute_D {t z : X} (ht : t ∈ d.S) (hz : z ∈ d.D)
    (hb : (d.nfc z).2.1 ≠ 0) (hc : t * z = z * t) : (d.nfc t).1 = 0 := by
  have hc1 : ⁅t, z⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hc
  have hnF : d.x₃ (d.nfc z).2.2.1 * (d.x₄ (d.nfc z).2.2.2.1 * d.x₅ (d.nfc z).2.2.2.2.1 *
      d.x₆ (d.nfc z).2.2.2.2.2) ∈ d.F :=
    mul_mem (d.x₃_mem_F _) (mul_mem (mul_mem (d.x₄_mem_F _) (d.x₅_mem_F _)) (d.x₆_mem_F _))
  have h : ⁅t, d.x₂ (d.nfc z).2.1 * (d.x₃ (d.nfc z).2.2.1 * (d.x₄ (d.nfc z).2.2.2.1 *
      d.x₅ (d.nfc z).2.2.2.2.1 * d.x₆ (d.nfc z).2.2.2.2.2))⁆ ∈ d.W := by
    rw [← mul_assoc, ← d.eq_nf_of_mem_D hz, hc1]
    exact one_mem _
  exact d.nfc_fst_eq_zero_of_comm_x₂_mem_W ht hb (d.comm_x₂_mem_W_of_comm_mem_W ht hnF h)

theorem mem_M_of_commute_M {t z : X} (ht : t ∈ d.S) (hz : z ∈ d.M) (ha : (d.nfc z).1 ≠ 0)
    (hc : t * z = z * t) : t ∈ d.M := by
  refine d.mem_M_of_mem_S_of_nfc_snd ht ?_
  have hc1 : ⁅z, t⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hc.symm
  obtain ⟨n, hn, hzn⟩ := d.eq_x₁_mul_of_mem_S (d.M_le_S hz)
  have hnF : n ∈ d.F := d.mem_F_of_mem_M_of_nfc_fst (by
      have := mul_mem (inv_mem (d.x₁_mem_M (d.nfc z).1)) hz
      rwa [inv_mul_eq_of_eq_mul hzn] at this) (d.nfc_fst_of_mem_D hn)
  have h1 : ⁅d.x₁ (d.nfc z).1, t⁆ ∈ d.W := by
    have h := hc1 ▸ (one_mem d.W : (1 : X) ∈ d.W)
    rw [hzn, commutatorElement_mul_mem_iff (d.S_le_normalizer_W (d.U₁_le_S (d.x₁_mem_U₁ _)))
      (commutatorElement_mem_comm.1 (d.commutator_S_F (commutator_mem_commutator ht hnF)))] at h
    exact h
  have hn'F : d.x₃ (d.nfc t).2.2.1 * (d.x₄ (d.nfc t).2.2.2.1 * d.x₅ (d.nfc t).2.2.2.2.1 *
      d.x₆ (d.nfc t).2.2.2.2.2) ∈ d.F :=
    mul_mem (d.x₃_mem_F _) (mul_mem (mul_mem (d.x₄_mem_F _) (d.x₅_mem_F _)) (d.x₆_mem_F _))
  have ht' : t = d.x₁ (d.nfc t).1 * (d.x₂ (d.nfc t).2.1 * (d.x₃ (d.nfc t).2.2.1 *
      (d.x₄ (d.nfc t).2.2.2.1 * d.x₅ (d.nfc t).2.2.2.2.1 * d.x₆ (d.nfc t).2.2.2.2.2))) := by
    conv_lhs => rw [d.eq_nf_of_mem_S ht]
    group
  rw [ht', commutatorElement_mul_right_conj,
    commutatorElement_eq_one_iff_commute.2 (commute_of_add d.x₁_add _ _), one_mul] at h1
  have h2 : ⁅d.x₁ (d.nfc z).1, d.x₂ (d.nfc t).2.1 * (d.x₃ (d.nfc t).2.2.1 *
      (d.x₄ (d.nfc t).2.2.2.1 * d.x₅ (d.nfc t).2.2.2.2.1 * d.x₆ (d.nfc t).2.2.2.2.2))⁆ ∈ d.W := by
    have := (mem_normalizer_iff''.1 (d.S_le_normalizer_W (d.U₁_le_S
      (d.x₁_mem_U₁ (d.nfc t).1))) _).1 h1
    simpa [mul_assoc] using this
  have h3 := d.comm_x₂_mem_W_of_comm_mem_W (d.U₁_le_S (d.x₁_mem_U₁ _)) hn'F h2
  exact Subtype.ext ((mul_eq_zero.1 (d.mul_eq_zero_of_comm₁₂_mem_W h3)).resolve_left ha)

theorem v_normalizes_M : d.v ∈ normalizer (d.M : Set X) := by
  have := d.finite
  refine mem_normalizer_fintype (conj_mem_sup ?_ (conj_mem_sup ?_ ?_))
  · rintro _ ⟨a, rfl⟩
    rw [d.v_conj_x₁]
    exact d.F_le_M (d.x₃_mem_F a)
  · rintro _ ⟨a, rfl⟩
    rw [d.v_conj_x₃]
    exact d.x₁_mem_M a
  · intro w hw
    exact d.F_le_M (d.W_le_F ((mem_normalizer_iff.1 d.v_normalizes_W w).1 hw))

theorem card_le_of_commute_D_of_ne {T : Subgroup X} {z : X} (hTS : T ≤ d.S) (hz : z ∈ d.D)
    (hb : (d.nfc z).2.1 ≠ 0) (hTz : ∀ t ∈ T, t * z = z * t) : Nat.card T ≤ q ^ 8 := by
  classical
  have hTD : ∀ t ∈ T, (d.nfc t).1 = 0 := fun t ht =>
    d.nfc_fst_eq_zero_of_commute_D (hTS ht) hz hb (hTz t ht)
  have h5 : ∀ t ∈ T, (d.nfc z).2.1 * (d.nfc t).2.2.2.2.1 =
      d.tr ((d.nfc z).2.2.1 * (d.nfc t).2.2.2.1) +
      (d.tr ((d.nfc t).2.2.1 * (d.nfc z).2.2.2.1) + (d.nfc t).2.1 * (d.nfc z).2.2.2.2.1) := by
    intro t ht
    have hc := hTz t ht
    rw [← commutatorElement_eq_one_iff_mul_comm,
      d.eq_nf_of_mem_D (d.mem_D_of_nfc_fst (hTS ht) (hTD t ht)), d.eq_nf_of_mem_D hz,
      d.comm_D_D_formula, d.x₆_eq_one_iff] at hc
    exact CharTwo.add_eq_zero.1 hc
  let G : T → d.Γ₀ × d.Γ × d.Γ × d.Γ₀ := fun t =>
    ((d.nfc t).2.1, (d.nfc t).2.2.1, (d.nfc t).2.2.2.1, (d.nfc t).2.2.2.2.2)
  have hG : Function.Injective G := by
    intro t t' h
    simp only [G, Prod.mk.injEq] at h
    obtain ⟨h2, h3, h4, h6⟩ := h
    have h5' : (d.nfc (t : X)).2.2.2.2.1 = (d.nfc (t' : X)).2.2.2.2.1 := by
      have e := h5 t t.2
      have e' := h5 t' t'.2
      rw [h2, h3, h4, ← e'] at e
      exact mul_left_cancel₀ hb e
    apply Subtype.ext
    rw [← d.nf_nfc (hTS t.2), ← d.nf_nfc (hTS t'.2)]
    exact congrArg d.nf (Prod.ext ((hTD t t.2).trans (hTD t' t'.2).symm)
      (Prod.ext h2 (Prod.ext h3 (Prod.ext h4 (Prod.ext h5' h6)))))
  have h := Nat.card_le_card_of_injective G hG
  simp only [Nat.card_prod, d.card_Γ, d.card_Γ₀] at h
  calc Nat.card T ≤ q * (q ^ 3 * (q ^ 3 * q)) := h
    _ = q ^ 8 := by ring

@[expose] noncomputable def tripleBilin : LinearMap.BilinForm d.Γ₀ (d.Γ₀ × d.Γ × d.Γ) :=
  (LinearMap.mul d.Γ₀ d.Γ₀).compl₁₂ (LinearMap.fst _ _ _) (LinearMap.fst _ _ _) +
    d.trBilin.compl₁₂ ((LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _))
      ((LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _)) +
    d.trBilin.compl₁₂ ((LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _))
      ((LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _))

theorem tripleBilin_apply (x y : d.Γ₀ × d.Γ × d.Γ) :
    d.tripleBilin x y = x.1 * y.1 + d.tr (x.2.1 * y.2.1) + d.tr (x.2.2 * y.2.2) :=
  rfl

theorem tripleBilin_nondegenerate : d.tripleBilin.Nondegenerate := by
  have h0 : d.tr 0 = 0 := Subtype.ext (by rw [coe_fixedTrace]; simp)
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have h1 := hx (1, 0, 0)
    rw [tripleBilin_apply, mul_zero, mul_zero, mul_one, h0, add_zero, add_zero] at h1
    refine Prod.ext h1 (Prod.ext (d.eq_zero_of_forall_tr_mul fun t => ?_)
      (d.eq_zero_of_forall_tr_mul fun t => ?_))
    · have := hx (0, t, 0)
      rwa [tripleBilin_apply, mul_zero, mul_zero, h0, zero_add, add_zero] at this
    · have := hx (0, 0, t)
      rwa [tripleBilin_apply, mul_zero, mul_zero, h0, zero_add, zero_add] at this
  · have h1 := hy (1, 0, 0)
    rw [tripleBilin_apply, zero_mul, zero_mul, one_mul, h0, add_zero, add_zero] at h1
    refine Prod.ext h1 (Prod.ext (d.eq_zero_of_forall_tr_mul fun t => ?_)
      (d.eq_zero_of_forall_tr_mul fun t => ?_))
    · have := hy (0, t, 0)
      rwa [tripleBilin_apply, zero_mul, zero_mul, h0, zero_add, add_zero, mul_comm] at this
    · have := hy (0, 0, t)
      rwa [tripleBilin_apply, zero_mul, zero_mul, h0, zero_add, zero_add, mul_comm] at this

theorem qComm_eq_zero_of_commute_F {t z : X} (ht : t ∈ d.S) (hz : z ∈ d.F) (hc : t * z = z * t) :
    d.qComm (d.nfc t).1 (d.nfc z).2.2.1 = 0 := by
  obtain ⟨m, hm, htm⟩ := d.eq_x₁_mul_of_mem_S ht
  have hc1 : ⁅t, z⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hc
  have h : ⁅d.x₁ (d.nfc t).1, z⁆ ∈ d.Y := by
    have h := hc1 ▸ (one_mem d.Y : (1 : X) ∈ d.Y)
    rw [htm, commutatorElement_mul_mem_iff (d.S_le_normalizer_Y (d.U₁_le_S (d.x₁_mem_U₁ _)))
      (d.V_le_Y (d.commutator_D_D (commutator_mem_commutator hm (d.F_le_D hz))))] at h
    exact h
  have hzF : z = d.x₃ (d.nfc z).2.2.1 * d.x₄ (d.nfc z).2.2.2.1 *
      (d.x₅ (d.nfc z).2.2.2.2.1 * d.x₆ (d.nfc z).2.2.2.2.2) := by
    conv_lhs => rw [d.eq_nf_of_mem_D (d.F_le_D hz)]
    rw [show (d.nfc z).2.1 = 0 from ?_, d.x₂_zero, one_mul]
    · group
    · obtain ⟨c, w, hw, hcw⟩ := d.mem_F_iff.1 hz
      rw [← hcw, show d.x₃ c * w = d.x₂ 0 * d.x₃ c * w by rw [d.x₂_zero, one_mul]]
      exact (d.nfc_x₂_x₃_mul hw).1
  rw [hzF, d.comm_x₁_F _ _ _ (mul_mem (d.x₅_mem_Y _) (d.x₆_mem_Y _)), mul_assoc,
    mul_mem_cancel_right (mul_mem (d.x₅_mem_Y _) (d.x₆_mem_Y _)), d.x₄_mem_Y_iff] at h
  exact h

theorem qComm_comm (a c : d.Γ) : d.qComm a c = d.qComm c a := by
  simp only [qComm]
  ring

theorem nfc_of_mem_F {z : X} (hz : z ∈ d.F) : (d.nfc z).1 = 0 ∧ (d.nfc z).2.1 = 0 := by
  obtain ⟨c, w, hw, rfl⟩ := d.mem_F_iff.1 hz
  refine ⟨d.nfc_fst_of_mem_D (d.F_le_D (mul_mem (d.x₃_mem_F c) (d.W_le_F hw))), ?_⟩
  rw [show d.x₃ c * w = d.x₂ 0 * d.x₃ c * w by rw [d.x₂_zero, one_mul]]
  exact (d.nfc_x₂_x₃_mul hw).1

theorem mem_W_of_mem_F_of_nfc {z : X} (hz : z ∈ d.F) (h : (d.nfc z).2.2.1 = 0) : z ∈ d.W := by
  rw [d.eq_nf_of_mem_D (d.F_le_D hz), (d.nfc_of_mem_F hz).2, h, d.x₂_zero, d.x₃_zero, one_mul,
    one_mul]
  exact mul_mem (mul_mem (d.x₄_mem_W _) (d.x₅_mem_W _)) (d.x₆_mem_W _)

theorem card_le_of_le_F_of_not_le_W {Z₀ T : Subgroup X} (hZF : Z₀ ≤ d.F) (hZW : ¬ Z₀ ≤ d.W)
    (hZ : q ^ 2 < Nat.card Z₀) (hTS : T ≤ d.S) (hTZ : ∀ t ∈ T, ∀ z ∈ Z₀, t * z = z * t) :
    Nat.card T ≤ q ^ 8 := by
  classical
  have := d.finite
  have hq2 := d.two_le_q
  have hq1 : 1 < q := by omega
  obtain ⟨z₀, hz₀Z, hz₀W⟩ := Set.not_subset.1 hZW
  have hc₀ : (d.nfc z₀).2.2.1 ≠ 0 := fun h => hz₀W (d.mem_W_of_mem_F_of_nfc (hZF hz₀Z) h)
  let φ : T →* Multiplicative d.Γ :=
    { toFun := fun t => Multiplicative.ofAdd (d.nfc t).1
      map_one' := by
        change Multiplicative.ofAdd (d.nfc 1).1 = 1
        rw [d.nfc_one]
        rfl
      map_mul' := fun t t' => by
        change Multiplicative.ofAdd (d.nfc ((t : X) * t')).1 = _
        rw [d.nfc_fst_mul (hTS t.2) (hTS t'.2)]
        rfl }
  have hcard := card_eq_card_range_mul_card_ker φ
  have hrange : Nat.card φ.range ≤ q := by
    have hfix : ∀ y : φ.range, d.σ (Multiplicative.toAdd (y : Multiplicative d.Γ) /
        (d.nfc z₀).2.2.1) = Multiplicative.toAdd (y : Multiplicative d.Γ) / (d.nfc z₀).2.2.1 := by
      rintro ⟨_, ⟨t, rfl⟩⟩
      refine d.σ_div_eq_of_qComm hc₀ ?_
      rw [d.qComm_comm]
      exact d.qComm_eq_zero_of_commute_F (hTS t.2) (hZF hz₀Z) (hTZ t t.2 z₀ hz₀Z)
    calc Nat.card φ.range ≤ Nat.card d.Γ₀ := by
          refine Nat.card_le_card_of_injective (fun y => ⟨_, hfix y⟩) fun y y' h => ?_
          have h' := congrArg Subtype.val h
          simp only at h'
          rw [div_left_inj' hc₀] at h'
          exact Subtype.ext h'
      _ = q := d.card_Γ₀
  set P := AddSubgroup.closure {p | ∃ z ∈ Z₀,
    ((d.nfc z).2.2.2.2.1, (d.nfc z).2.2.2.1, (d.nfc z).2.2.1) = p} with hP
  have hZP : Nat.card Z₀ ≤ Nat.card P * q := by
    refine le_trans ?_ (le_of_eq (show Nat.card (P × d.Γ₀) = Nat.card P * q by
      rw [Nat.card_prod, d.card_Γ₀]))
    refine Nat.card_le_card_of_injective (fun z => (⟨((d.nfc z).2.2.2.2.1, (d.nfc z).2.2.2.1,
      (d.nfc z).2.2.1), AddSubgroup.subset_closure ⟨z, z.2, rfl⟩⟩, (d.nfc z).2.2.2.2.2))
      fun z z' h => ?_
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨⟨h5, h4, h3⟩, h6⟩ := h
    apply Subtype.ext
    rw [← d.nf_nfc (d.F_le_S (hZF z.2)), ← d.nf_nfc (d.F_le_S (hZF z'.2))]
    obtain ⟨a1, a2⟩ := d.nfc_of_mem_F (hZF z.2)
    obtain ⟨b1, b2⟩ := d.nfc_of_mem_F (hZF z'.2)
    exact congrArg d.nf (Prod.ext (a1.trans b1.symm) (Prod.ext (a2.trans b2.symm)
      (Prod.ext h3 (Prod.ext h4 (Prod.ext h5 h6)))))
  have hkerD : ∀ t : φ.ker, (t : X) ∈ d.D := fun t => by
    have h := congrArg Multiplicative.toAdd (MonoidHom.mem_ker.1 t.2)
    exact d.mem_D_of_nfc_fst (hTS t.1.2) h
  have horth : ∀ t : φ.ker, ∀ s ∈ P,
      d.tripleBilin s ((d.nfc t).2.1, (d.nfc t).2.2.1, (d.nfc t).2.2.2.1) = 0 := by
    intro t s hs
    induction hs using AddSubgroup.closure_induction with
    | mem s hs =>
      obtain ⟨z, hz, rfl⟩ := hs
      have hc := hTZ t t.1.2 z hz
      rw [← commutatorElement_eq_one_iff_mul_comm, d.eq_nf_of_mem_D (hkerD t),
        d.eq_nf_of_mem_D (d.F_le_D (hZF hz)), (d.nfc_of_mem_F (hZF hz)).2, d.comm_D_D_formula,
        d.x₆_eq_one_iff, zero_mul, zero_add] at hc
      rw [tripleBilin_apply, mul_comm (d.nfc z).2.2.2.2.1, mul_comm (d.nfc z).2.2.2.1, ← hc]
      ring
    | zero => simp
    | add s s' _ _ hs hs' => rw [map_add, LinearMap.add_apply, hs, hs', add_zero]
    | neg s _ hs => rw [map_neg, LinearMap.neg_apply, hs, neg_zero]
  let G : φ.ker → {w : d.Γ₀ × d.Γ × d.Γ // ∀ s ∈ P, d.tripleBilin s w = 0} × d.Γ₀ × d.Γ₀ :=
    fun t => (⟨((d.nfc t).2.1, (d.nfc t).2.2.1, (d.nfc t).2.2.2.1), horth t⟩,
      (d.nfc t).2.2.2.2.1, (d.nfc t).2.2.2.2.2)
  have hG : Function.Injective G := by
    intro t t' h
    simp only [G, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨⟨h2, h3, h4⟩, h5, h6⟩ := h
    apply Subtype.ext; apply Subtype.ext
    rw [← d.nf_nfc (hTS t.1.2), ← d.nf_nfc (hTS t'.1.2)]
    exact congrArg d.nf (Prod.ext ((d.nfc_fst_of_mem_D (hkerD t)).trans
      (d.nfc_fst_of_mem_D (hkerD t')).symm) (Prod.ext h2 (Prod.ext h3 (Prod.ext h4
        (Prod.ext h5 h6)))))
  have hker := Nat.card_le_card_of_injective G hG
  rw [Nat.card_prod, Nat.card_prod, d.card_Γ₀] at hker
  have hA := card_span_mul_card_orth_eq d.tripleBilin d.tripleBilin_nondegenerate P
  rw [Nat.card_prod, Nat.card_prod, d.card_Γ₀, d.card_Γ] at hA
  have hn := d.card_Γ₀_submodule (Submodule.span d.Γ₀ (P : Set (d.Γ₀ × d.Γ × d.Γ)))
  set k := Module.finrank d.Γ₀ (Submodule.span d.Γ₀ (P : Set (d.Γ₀ × d.Γ × d.Γ)))
  have hPn : Nat.card P ≤ q ^ k := by
    rw [← hn]
    exact Nat.card_le_card_of_injective (fun p => ⟨p, Submodule.subset_span p.2⟩)
      fun p p' h => Subtype.ext (congrArg Subtype.val h :)
  have hk2 : 2 ≤ k := by
    by_contra h
    push Not at h
    have : q ^ k ≤ q ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_one] at this
    have : Nat.card Z₀ ≤ q * q := hZP.trans (Nat.mul_le_mul_right _ (hPn.trans this))
    nlinarith
  rw [hn] at hA
  set o := Nat.card {w : d.Γ₀ × d.Γ × d.Γ // ∀ s ∈ P, d.tripleBilin s w = 0}
  have ho : o ≤ q ^ 5 := by
    have h1 : q ^ 2 * o ≤ q ^ k * o := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hk2)
    rw [hA] at h1
    have h2 : q ^ 2 * o ≤ q ^ 2 * q ^ 5 := by
      calc q ^ 2 * o ≤ q * (q ^ 3 * q ^ 3) := h1
        _ = q ^ 2 * q ^ 5 := by ring
    exact Nat.le_of_mul_le_mul_left h2 (by positivity)
  calc Nat.card T = Nat.card φ.range * Nat.card φ.ker := hcard
    _ ≤ q * (q ^ 5 * (q * q)) := Nat.mul_le_mul hrange (hker.trans (Nat.mul_le_mul_right _ ho))
    _ = q ^ 8 := by ring

theorem le_W_of_large_centralizer {Z₀ T : Subgroup X} (hZS : Z₀ ≤ d.S)
    (hZc : ∀ x ∈ Z₀, ∀ y ∈ Z₀, x * y = y * x) (hZ2 : ∀ z ∈ Z₀, z * z = 1)
    (hZ : q ^ 2 < Nat.card Z₀) (hTS : T ≤ d.S) (hTZ : ∀ t ∈ T, ∀ z ∈ Z₀, t * z = z * t)
    (hT : q ^ 8 < Nat.card T) : Z₀ ≤ d.W := by
  have hFcase : ∀ {Z₁ T₁ : Subgroup X}, Z₁ ≤ d.F → q ^ 2 < Nat.card Z₁ → T₁ ≤ d.S →
      (∀ t ∈ T₁, ∀ z ∈ Z₁, t * z = z * t) → q ^ 8 < Nat.card T₁ → Z₁ ≤ d.W :=
    fun hZF hZ' hTS' hTZ' hT' => by
      by_contra hW
      exact absurd (d.card_le_of_le_F_of_not_le_W hZF hW hZ' hTS' hTZ') (not_le.2 hT')
  by_cases hF : Z₀ ≤ d.F
  · exact hFcase hF hZ hTS hTZ hT
  exfalso
  obtain ⟨z, hzZ, hzF⟩ := Set.not_subset.1 hF
  rcases le_or_le_of_forall_mem_or_mem (E := Z₀) (A := d.D) (B := d.M) (fun z hz =>
    d.mem_D_or_mem_M_of_mul_self_mem_W (hZS hz) (by rw [hZ2 z hz]; exact one_mem _)) with hD | hM
  · have hb : (d.nfc z).2.1 ≠ 0 := fun h => hzF (d.mem_F_of_mem_D_of_nfc_snd (hD hzZ) h)
    exact absurd (d.card_le_of_commute_D_of_ne hTS (hD hzZ) hb fun t ht => hTZ t ht z hzZ)
      (not_le.2 hT)
  · have ha : (d.nfc z).1 ≠ 0 := fun h => hzF (d.mem_F_of_mem_M_of_nfc_fst (hM hzZ) h)
    have hTM : ∀ t ∈ T, t ∈ d.M := fun t ht =>
      d.mem_M_of_commute_M (hTS ht) (hM hzZ) ha (hTZ t ht z hzZ)
    obtain ⟨x, hxU, hx⟩ := d.yamada_3_11_2_conj hM hZc hZ2 hF
    set g := x * d.v with hg
    have hxS : x ∈ d.S := d.U₂_le_S hxU
    have hgM : g ∈ normalizer (d.M : Set X) := mul_mem (d.S_le_normalizer_M hxS) d.v_normalizes_M
    have hgW : g ∈ normalizer (d.W : Set X) := mul_mem (d.S_le_normalizer_W hxS) d.v_normalizes_W
    set c := MulAut.conj g⁻¹ with hc
    have hcapp : ∀ y, c y = g⁻¹ * y * g := fun y => by
      rw [hc, MulAut.conj_apply, inv_inv]
    have hZ' : Z₀.map c.toMonoidHom ≤ d.F := by
      rintro _ ⟨y, hy, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hcapp]
      exact hx y hy
    have hT' : T.map c.toMonoidHom ≤ d.S := by
      rintro _ ⟨y, hy, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hcapp]
      exact d.M_le_S ((mem_normalizer_iff''.1 hgM y).1 (hTM y hy))
    have hW' := hFcase hZ' (by rwa [card_map_of_injective c.injective]) hT'
      (by
        rintro _ ⟨t, ht, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [← map_mul, ← map_mul, hTZ t ht y hy]) (by rwa [card_map_of_injective c.injective])
    have hzW : g⁻¹ * z * g ∈ d.W := by
      rw [← hcapp]
      exact hW' ⟨z, hzZ, rfl⟩
    exact hzF (d.W_le_F ((mem_normalizer_iff''.1 hgW z).2 hzW))

@[expose] def centSx₄Y (α : d.Γ) : Subgroup X :=
  d.S ⊓ centralizer (insert (d.x₄ α) (d.Y : Set X))

@[expose] noncomputable def zSx₄Y (α : d.Γ) : Subgroup X :=
  (tripleHom (x := fun l : d.Γ₀ => d.x₄ ((l : d.Γ) * α)) (fun a b => by
      rw [Subfield.coe_add, add_mul, d.x₄_add]) d.x₅_add d.x₆_add
    (fun a b => d.commute₄₅ _ b) (fun a c => d.commute₄₆ _ c) d.commute₅₆).range

theorem mem_centSx₄Y_iff {α : d.Γ} {t : X} :
    t ∈ d.centSx₄Y α ↔ t ∈ d.S ∧ (d.nfc t).2.1 = 0 ∧ d.tr ((d.nfc t).1 * α) = 0 ∧
      d.tr ((d.nfc t).2.2.1 * α) = 0 := by
  rw [centSx₄Y, mem_inf, mem_centralizer_iff]
  refine and_congr_right fun ht => ?_
  have h4 := d.mem_centralizer_W_iff ht α 0 0
  rw [d.x₅_zero, d.x₆_zero, mul_one, mul_one, mem_centralizer_singleton_iff, mul_zero,
    add_zero] at h4
  constructor
  · intro h
    have hY := d.mem_centralizer_W_iff ht 0 1 0
    rw [d.x₄_zero, d.x₆_zero, one_mul, mul_one, mem_centralizer_singleton_iff, mul_zero,
      mul_one] at hY
    have hY' := (hY.1 (h _ (Set.mem_insert_of_mem _ (d.x₅_mem_Y 1))).symm).2
    have h0 : d.tr 0 = 0 := Subtype.ext (by rw [coe_fixedTrace]; simp)
    rw [mul_zero, h0, zero_add] at hY'
    obtain ⟨h1, h2⟩ := h4.1 (h _ (Set.mem_insert _ _)).symm
    exact ⟨hY', h1, h2⟩
  · rintro ⟨hb, h1, h2⟩ y hy
    rcases Set.mem_insert_iff.1 hy with rfl | hy
    · exact (h4.2 ⟨h1, h2⟩).symm
    · obtain ⟨f, g, rfl⟩ := d.mem_Y_coords hy
      have hY := d.mem_centralizer_W_iff ht 0 f g
      rw [mem_centralizer_singleton_iff] at hY
      have h0 : d.tr 0 = 0 := Subtype.ext (by rw [coe_fixedTrace]; simp)
      have := (hY.2 ⟨by rw [mul_zero, h0], by rw [mul_zero, h0, hb, zero_mul, add_zero]⟩).symm
      simpa only [nf_apply, d.x₁_zero, d.x₂_zero, d.x₃_zero, d.x₄_zero, one_mul] using this

theorem card_tr_mul_eq_zero {α : d.Γ} (hα : α ≠ 0) :
    Nat.card {a : d.Γ // d.tr (a * α) = 0} = q ^ 2 := by
  set L := (Submodule.span d.Γ₀ {α}).toAddSubgroup with hL
  have h1 := card_span_mul_card_orth_eq d.trBilin d.trBilin_nondegenerate L
  rw [d.card_Γ, show Submodule.span d.Γ₀ ((L : AddSubgroup d.Γ) : Set d.Γ) =
    Submodule.span d.Γ₀ {α} from Submodule.span_eq _, d.card_span_singleton_Γ₀ hα] at h1
  have h2 : Nat.card {a : d.Γ // ∀ s ∈ L, d.trBilin s a = 0} = q ^ 2 := by
    have h : q * Nat.card {a : d.Γ // ∀ s ∈ L, d.trBilin s a = 0} = q * q ^ 2 := by
      rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left (by have := d.two_le_q; omega) h
  rw [← h2]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ⟨fun h s hs => ?_, fun h => ?_⟩)
  · obtain ⟨l, rfl⟩ := Submodule.mem_span_singleton.1 hs
    rw [map_smul, LinearMap.smul_apply, trBilin_apply, mul_comm, h, smul_zero]
  · have := h α (Submodule.subset_span (Set.mem_singleton α))
    rwa [trBilin_apply, mul_comm] at this

theorem card_centSx₄Y {α : d.Γ} (hα : α ≠ 0) : Nat.card (d.centSx₄Y α) = q ^ 9 := by
  have h := d.card_eq_of_nf (T := d.centSx₄Y α)
    (α := {a : d.Γ // d.tr (a * α) = 0} × {c : d.Γ // d.tr (c * α) = 0} × d.Γ × d.Γ₀ × d.Γ₀)
    (fun p => (p.1.1, 0, p.2.1.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2))
    (fun p p' h => by
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, -, h3, h4, h5, h6⟩ := h
      exact Prod.ext (Subtype.ext h1) (Prod.ext (Subtype.ext h3) (Prod.ext h4 (Prod.ext h5 h6))))
    (fun p => by
      rw [d.mem_centSx₄Y_iff, nfc_nf]
      exact ⟨d.normal_form.mapsTo (Set.mem_univ _), rfl, p.1.2, p.2.1.2⟩)
    (fun g hg => by
      obtain ⟨hgS, h2, h1, h3⟩ := d.mem_centSx₄Y_iff.1 hg
      refine ⟨(⟨(d.nfc g).1, h1⟩, ⟨(d.nfc g).2.2.1, h3⟩, (d.nfc g).2.2.2.1, (d.nfc g).2.2.2.2.1,
        (d.nfc g).2.2.2.2.2), ?_⟩
      show d.nf ((d.nfc g).1, 0, (d.nfc g).2.2.1, (d.nfc g).2.2.2.1, (d.nfc g).2.2.2.2.1,
        (d.nfc g).2.2.2.2.2) = g
      rw [← h2]
      exact d.nf_nfc hgS)
  rw [h, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod, d.card_tr_mul_eq_zero hα,
    d.card_Γ, d.card_Γ₀]
  ring

theorem W_le_centSx₄Y (α : d.Γ) : d.W ≤ d.centSx₄Y α := by
  intro w hw
  obtain ⟨-, h1, h2, h3⟩ := d.eq_nf_of_mem_W hw
  have h0 : d.tr 0 = 0 := Subtype.ext (by rw [coe_fixedTrace]; simp)
  rw [d.mem_centSx₄Y_iff, h1, h2, h3, zero_mul, h0]
  exact ⟨d.W_le_S hw, rfl, rfl, rfl⟩

theorem centSx₄Y_inf_centralizer {α : d.Γ} (hα : α ≠ 0) :
    d.centSx₄Y α ⊓ centralizer (d.centSx₄Y α : Set X) = d.zSx₄Y α := by
  classical
  have := d.finite
  have h0 : d.tr 0 = 0 := Subtype.ext (by rw [coe_fixedTrace]; simp)
  apply le_antisymm
  · intro z hz'
    obtain ⟨hz, hzc⟩ := mem_inf.1 hz'
    rw [mem_centralizer_iff] at hzc
    obtain ⟨hzS, hb, -, -⟩ := d.mem_centSx₄Y_iff.1 hz
    have hW : ∀ e : d.Γ, d.tr ((d.nfc z).1 * e) = 0 ∧ d.tr ((d.nfc z).2.2.1 * e) = 0 := by
      intro e
      have h := (d.mem_centralizer_W_iff hzS e 0 0).1 (mem_centralizer_singleton_iff.2
        (hzc _ (d.W_le_centSx₄Y α (mul_mem (mul_mem (d.x₄_mem_W e) (d.x₅_mem_W 0))
          (d.x₆_mem_W 0)))).symm)
      rwa [mul_zero, add_zero] at h
    have ha : (d.nfc z).1 = 0 := d.eq_zero_of_forall_tr_mul fun e => (hW e).1
    have hc : (d.nfc z).2.2.1 = 0 := d.eq_zero_of_forall_tr_mul fun e => (hW e).2
    have hzW :
        z = d.x₄ (d.nfc z).2.2.2.1 * d.x₅ (d.nfc z).2.2.2.2.1 * d.x₆ (d.nfc z).2.2.2.2.2 := by
      conv_lhs => rw [d.eq_nf_of_mem_S hzS, ha, hb, hc]
      rw [d.x₁_zero, d.x₂_zero, d.x₃_zero]
      group
    set e := (d.nfc z).2.2.2.1 with he
    set f := (d.nfc z).2.2.2.2.1 with hf
    set g := (d.nfc z).2.2.2.2.2 with hg
    have horth : ∀ a : d.Γ, d.tr (a * α) = 0 → d.tr (a * e) = 0 := by
      intro a ha'
      have hx₁ : d.x₁ a ∈ d.centSx₄Y α := by
        rw [d.mem_centSx₄Y_iff]
        refine ⟨d.U₁_le_S (d.x₁_mem_U₁ a), ?_⟩
        rw [← d.nf_x₁, nfc_nf]
        exact ⟨rfl, ha', by rw [zero_mul, h0]⟩
      have h := (d.mem_centralizer_W_iff (d.U₁_le_S (d.x₁_mem_U₁ a)) e f g).1 (by
          rw [mem_centralizer_singleton_iff, ← hzW]
          exact hzc _ hx₁)
      rw [← d.nf_x₁, nfc_nf] at h
      exact h.1
    have heα : e ∈ Submodule.span d.Γ₀ {α} := by
      set A := LinearMap.ker (d.trBilin α) with hA
      have hAc : Nat.card A = q ^ 2 := by
        rw [← d.card_tr_mul_eq_zero hα]
        refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
        rw [LinearMap.mem_ker, trBilin_apply, mul_comm]
      have h1 := card_span_mul_card_orth_eq d.trBilin d.trBilin_nondegenerate A.toAddSubgroup
      rw [d.card_Γ, show Submodule.span d.Γ₀ ((A.toAddSubgroup : AddSubgroup d.Γ) : Set d.Γ) = A
        from Submodule.span_eq _, hAc] at h1
      set B := {e' : d.Γ | ∀ s ∈ A.toAddSubgroup, d.trBilin s e' = 0} with hB
      have hBc : Nat.card B = q := by
        have h : q ^ 2 * Nat.card B = q ^ 2 * q := by
          change q ^ 2 * Nat.card {z : d.Γ // ∀ s ∈ A.toAddSubgroup, d.trBilin s z = 0} = _
          rw [h1]; ring
        exact Nat.eq_of_mul_eq_mul_left (by have := d.two_le_q; positivity) h
      have hsub : (Submodule.span d.Γ₀ {α} : Set d.Γ) ⊆ B := by
        intro e' he'
        obtain ⟨l, rfl⟩ := Submodule.mem_span_singleton.1 he'
        intro s hs
        rw [map_smul, trBilin_apply, smul_eq_mul]
        have : d.tr (s * α) = 0 := by
          have := LinearMap.mem_ker.1 hs
          rwa [trBilin_apply, mul_comm] at this
        rw [this, mul_zero]
      have heB : e ∈ B := fun s hs => by
        rw [trBilin_apply]
        exact horth s (by
          have := LinearMap.mem_ker.1 hs
          rwa [trBilin_apply, mul_comm] at this)
      by_contra hne
      have hlt : (Submodule.span d.Γ₀ {α} : Set d.Γ) ⊂ B := ⟨hsub, fun h => hne (h heB)⟩
      have := Set.ncard_lt_ncard hlt (Set.toFinite _)
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hBc] at this
      change Nat.card (Submodule.span d.Γ₀ {α}) < q at this
      rw [d.card_span_singleton_Γ₀ hα] at this
      exact lt_irrefl _ this
    obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.1 heα
    refine ⟨Multiplicative.ofAdd (l, f, g), ?_⟩
    rw [hzW]
    change d.x₄ ((l : d.Γ) * α) * d.x₅ f * d.x₆ g = d.x₄ e * d.x₅ f * d.x₆ g
    rw [← hl, Algebra.smul_def]
    rfl
  · rintro _ ⟨⟨l, f, g⟩, rfl⟩
    change d.x₄ ((l : d.Γ) * α) * d.x₅ f * d.x₆ g ∈ _
    have hw : d.x₄ ((l : d.Γ) * α) * d.x₅ f * d.x₆ g ∈ d.W :=
      mul_mem (mul_mem (d.x₄_mem_W _) (d.x₅_mem_W f)) (d.x₆_mem_W g)
    refine ⟨d.W_le_centSx₄Y α hw, mem_centralizer_iff.2 fun t ht => ?_⟩
    obtain ⟨htS, hb, ha, hc⟩ := d.mem_centSx₄Y_iff.1 ht
    have key : ∀ a : d.Γ, d.tr (a * α) = 0 → d.tr (a * ((l : d.Γ) * α)) = 0 := fun a h =>
      Subtype.ext (by
        rw [mul_left_comm, d.tr_smul, h, ZeroMemClass.coe_zero, mul_zero])
    have := (d.mem_centralizer_W_iff htS _ f g).2 ⟨key _ ha, by rw [key _ hc, hb, zero_mul,
      add_zero]⟩
    exact (mem_centralizer_singleton_iff.1 this)

theorem exists_torus_map_centSx₄Y {α : d.Γ} (hα : α ≠ 0) :
    ∃ h ∈ d.J, (d.centSx₄Y α).map (MulAut.conj h).toMonoidHom = d.centSx₄Y 1 := by
  have := d.finite
  obtain ⟨p, hp⟩ := d.exists_torus_conj_x₄ (one_ne_zero : (1 : d.Γ) ≠ 0) hα
  set j := d.torus p with hj
  have hjS : j ∈ normalizer (d.S : Set X) := by
    rw [d.normalizer_S]
    exact (le_sup_right : d.J ≤ d.B) ⟨p, rfl⟩
  have hjY : j ∈ normalizer (d.Y : Set X) := d.J_le_normalizer_Y ⟨p, rfl⟩
  refine ⟨j, ⟨p, rfl⟩, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    obtain ⟨htS, htc⟩ := mem_inf.1 ht
    rw [mem_centralizer_iff] at htc
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine mem_inf.2 ⟨(mem_normalizer_iff.1 hjS t).1 htS, mem_centralizer_iff.2 fun y hy => ?_⟩
    have key : ∀ y' ∈ insert (d.x₄ α) (d.Y : Set X),
        j * y' * j⁻¹ * (j * t * j⁻¹) = j * t * j⁻¹ * (j * y' * j⁻¹) := fun y' hy' => by
      have h := htc y' hy'
      calc j * y' * j⁻¹ * (j * t * j⁻¹) = j * (y' * t) * j⁻¹ := by group
        _ = j * (t * y') * j⁻¹ := by rw [h]
        _ = j * t * j⁻¹ * (j * y' * j⁻¹) := by group
    rcases Set.mem_insert_iff.1 hy with rfl | hy
    · rw [← hp]
      exact key _ (Set.mem_insert _ _)
    · have hy' : j⁻¹ * y * j ∈ d.Y := (mem_normalizer_iff''.1 hjY y).1 hy
      have h := key _ (Set.mem_insert_of_mem _ hy')
      rwa [show j * (j⁻¹ * y * j) * j⁻¹ = y by group] at h
  · rw [card_map_of_injective (MulAut.conj j).injective, d.card_centSx₄Y hα,
      d.card_centSx₄Y one_ne_zero]

theorem yamada_3_11_4 {T Z₀ : Subgroup X} (hTS : T ≤ d.S) (hT : q ^ 8 < Nat.card T)
    (hZT : Z₀ ≤ T) (hZc : Z₀ ≤ centralizer (T : Set X)) (hZ : CFSG.Open.IsElemAbelian 2 Z₀)
    (hZcard : q ^ 2 < Nat.card Z₀) :
    ∃ α : d.Γ, α ≠ 0 ∧ T ≤ d.centSx₄Y α ∧ Z₀ ≤ d.zSx₄Y α ∧ (q ^ 9 ≤ Nat.card T → T = d.centSx₄Y α) ∧
      Nat.card (d.centSx₄Y α) = q ^ 9 ∧
      d.centSx₄Y α ⊓ centralizer (d.centSx₄Y α : Set X) = d.zSx₄Y α ∧
      ∃ h ∈ d.J, (d.centSx₄Y α).map (MulAut.conj h).toMonoidHom = d.centSx₄Y 1 := by
  have := d.finite
  have hZS : Z₀ ≤ d.S := hZT.trans hTS
  have hTZ : ∀ t ∈ T, ∀ z ∈ Z₀, t * z = z * t := fun t ht z hz =>
    (mem_centralizer_iff.1 (hZc hz) t ht)
  have hZcomm : ∀ x ∈ Z₀, ∀ y ∈ Z₀, x * y = y * x := fun x hx y hy => by
    have := hZ.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : Z₀) ⟨y, hy⟩)
  have hZ2 : ∀ z ∈ Z₀, z * z = 1 := fun z hz => by rw [← sq]; exact hZ.2 z hz
  have hZW := d.le_W_of_large_centralizer hZS hZcomm hZ2 hZcard hTS hTZ hT
  obtain ⟨α, hα, hZα, hTα⟩ := d.exists_of_le_W hZW hZcard hTS hTZ hT
  have hTle : T ≤ d.centSx₄Y α := fun t ht => by
    obtain ⟨h2, h1, h3⟩ := hTα t ht
    exact d.mem_centSx₄Y_iff.2 ⟨hTS ht, h2, h1, h3⟩
  have hcard := d.card_centSx₄Y hα
  refine ⟨α, hα, hTle, fun z hz => ?_, fun h9 => Subgroup.eq_of_le_of_card_ge hTle
    (by rw [hcard]; exact h9), hcard, d.centSx₄Y_inf_centralizer hα, d.exists_torus_map_centSx₄Y hα⟩
  obtain ⟨l, hl⟩ := hZα z hz
  obtain ⟨hzW, -⟩ := d.eq_nf_of_mem_W (hZW hz)
  refine ⟨Multiplicative.ofAdd (l, (d.nfc z).2.2.2.2.1, (d.nfc z).2.2.2.2.2), ?_⟩
  change d.x₄ ((l : d.Γ) * α) * d.x₅ _ * d.x₆ _ = z
  rw [← hl]
  exact hzW.symm

end TrialityD4Data

end CFSG.LocalAnalysis.EvenBN.TrialityD4
