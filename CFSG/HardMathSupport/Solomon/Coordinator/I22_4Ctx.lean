module

public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Norm
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Iso
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

variable {Ω : Type*} [Group Ω]

@[expose] def i224K (B L : Subgroup Ω) : Subgroup Ω := ⨆ (b : Ω) (_ : b ∈ B), i224Cj b L

@[expose] def i224W (p : ℕ) (B K : Subgroup Ω) : Subgroup Ω :=
  ⨆ (E : Subgroup Ω) (_ : E ≤ B ∧ Nat.card B ≤ p * Nat.card E), K ⊓ Subgroup.centralizer (E : Set Ω)

structure I224Ctx (p : ℕ) (B L : Subgroup Ω) : Prop where
  prime : p.Prime
  elem : CFSG.Open.IsElemAbelian p B
  quasi : CFSG.Open.IsQuasisimple ↥L
  dist : ∀ g ∈ B, ∀ g' ∈ B, i224Cj g L ≠ i224Cj g' L →
    ∀ x ∈ i224Cj g L, ∀ y ∈ i224Cj g' L, x * y = y * x
  gen : L ≤ ⨆ (F : Subgroup Ω)
    (_ : F ≤ B ⊓ Subgroup.normalizer (L : Set Ω) ∧
      Nat.card ↥(B ⊓ Subgroup.normalizer (L : Set Ω)) ≤ p * Nat.card F),
    L ⊓ Subgroup.centralizer (F : Set Ω)

theorem i224_elem_comm {p : ℕ} {B : Subgroup Ω} (hB : CFSG.Open.IsElemAbelian p B) {x y : Ω}
    (hx : x ∈ B) (hy : y ∈ B) : x * y = y * x := CFSG.Open.IsElemAbelian.comm hB hx hy

theorem i224K_conj {B L : Subgroup Ω} {b : Ω} (hb : b ∈ B) {x : Ω} (hx : x ∈ i224K B L) :
    b * x * b⁻¹ ∈ i224K B L := by
  have key : i224K B L ≤ (i224K B L).comap (MulAut.conj b).toMonoidHom := by
    refine iSup₂_le fun g hg y hy => ?_
    show b * y * b⁻¹ ∈ i224K B L
    have h1 : b * y * b⁻¹ ∈ i224Cj (b * g) L := by
      rw [mem_i224Cj]
      have := mem_i224Cj.1 hy
      have e : (b * g)⁻¹ * (b * y * b⁻¹) * (b * g) = g⁻¹ * y * g := by group
      rw [e]
      exact this
    exact Subgroup.mem_iSup_of_mem (b * g) (Subgroup.mem_iSup_of_mem (B.mul_mem hb hg) h1)
  exact key hx

theorem i224W_conj {p : ℕ} {B K : Subgroup Ω} (hB : CFSG.Open.IsElemAbelian p B)
    (hK : ∀ b ∈ B, ∀ x ∈ K, b * x * b⁻¹ ∈ K) {b : Ω} (hb : b ∈ B) {w : Ω}
    (hw : w ∈ i224W p B K) : b * w * b⁻¹ ∈ i224W p B K := by
  have key : i224W p B K ≤ (i224W p B K).comap (MulAut.conj b).toMonoidHom := by
    refine iSup₂_le fun E hE y hy => ?_
    show b * y * b⁻¹ ∈ i224W p B K
    refine Subgroup.mem_iSup_of_mem E (Subgroup.mem_iSup_of_mem hE ⟨hK b hb y hy.1, ?_⟩)
    show b * y * b⁻¹ ∈ Subgroup.centralizer (E : Set Ω)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have c1 : Commute h b := i224_elem_comm hB (hE.1 hh) hb
    have c2 : Commute h y := (Subgroup.mem_centralizer_iff.1 hy.2 h hh)
    exact ((c1.mul_right c2).mul_right c1.inv_right).eq
  exact key hw

theorem i224_conj_centralizer {M : Subgroup Ω} {b z : Ω}
    (hz : z ∈ Subgroup.centralizer (M : Set Ω)) :
    b * z * b⁻¹ ∈ Subgroup.centralizer ((i224Cj b M : Subgroup Ω) : Set Ω) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have h0 := Subgroup.mem_centralizer_iff.1 hz (b⁻¹ * h * b) (mem_i224Cj.1 hh)
  calc h * (b * z * b⁻¹) = b * ((b⁻¹ * h * b) * z) * b⁻¹ := by group
    _ = b * (z * (b⁻¹ * h * b)) * b⁻¹ := by rw [h0]
    _ = (b * z * b⁻¹) * h := by group

theorem i224Adm_conj {H W Q Q' : Subgroup Ω} (b : Ω) (hW : ∀ w ∈ W, b * w * b⁻¹ ∈ W)
    (hQ : ∀ q ∈ Q, b * q * b⁻¹ ∈ Q') {x : Ω} (hx : x ∈ i224Adm H W Q) :
    b * x * b⁻¹ ∈ i224Adm (i224Cj b H) W Q' := by
  obtain ⟨hxH, q, hq, hxq⟩ := mem_i224Adm.1 hx
  refine mem_i224Adm.2 ⟨mem_i224Cj.2 ?_, b * q * b⁻¹, ⟨hW q hq.1, hQ q hq.2⟩, ?_⟩
  · have e : b⁻¹ * (b * x * b⁻¹) * b = x := by group
    rw [e]
    exact hxH
  · have e : (b * x * b⁻¹)⁻¹ * (b * q * b⁻¹) = b * (x⁻¹ * q) * b⁻¹ := by group
    rw [e]
    exact i224_conj_centralizer hxq

variable {p : ℕ} {B L : Subgroup Ω}

theorem i224_norm_elt [Finite Ω] (hc : I224Ctx p B L) {R F : Subgroup Ω} (hRB : R ≤ B)
    (hRA : B ⊓ Subgroup.normalizer (L : Set Ω) ⊓ R = ⊥)
    (hFA : F ≤ B ⊓ Subgroup.normalizer (L : Set Ω))
    (hcard : Nat.card B ≤ p * (Nat.card F * Nat.card R)) {y : Ω}
    (hy : y ∈ L ⊓ Subgroup.centralizer (F : Set Ω)) :
    ∃ n ∈ i224W p B (i224K B L),
      (∀ g₀ ∈ R, ∃ z : Ω, (∀ u ∈ i224Cj g₀ L, u * z = z * u) ∧ n = (g₀ * y * g₀⁻¹) * z) ∧
      (∀ Y : Subgroup Ω, (∀ g ∈ R, ∀ y ∈ Y, ∀ u ∈ L, y * (g * u * g⁻¹) = (g * u * g⁻¹) * y) →
        ∀ y ∈ Y, y * n = n * y) := by
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy => i224_elem_comm hc.elem hx hy
  have hmemcj : ∀ g (x : Ω), x ∈ L → g * x * g⁻¹ ∈ i224Cj g L := fun g x hx => by
    rw [mem_i224Cj]
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [e]
    exact hx
  have hcomm : ∀ g ∈ R, ∀ g' ∈ R, g ≠ g' → ∀ x ∈ L, ∀ y ∈ L,
      (g * x * g⁻¹) * (g' * y * g'⁻¹) = (g' * y * g'⁻¹) * (g * x * g⁻¹) := by
    intro g hg g' hg' hne x hx y hy
    have hne' : i224Cj g L ≠ i224Cj g' L := by
      intro h
      have h1 := mem_normalizer_of_i224Cj_eq h
      have h2 : g⁻¹ * g' ∈ B ⊓ Subgroup.normalizer (L : Set Ω) ⊓ R :=
        ⟨⟨B.mul_mem (B.inv_mem (hRB hg)) (hRB hg'), h1⟩, R.mul_mem (R.inv_mem hg) hg'⟩
      rw [hRA, Subgroup.mem_bot] at h2
      exact hne (inv_mul_eq_one.1 h2)
    exact hc.dist g (hRB hg) g' (hRB hg') hne' _ (hmemcj g x hx) _ (hmemcj g' y hy)
  obtain ⟨N, hN1, hN2, hN3, hN4, hN5⟩ := i224_exists_norm L R hcomm
  have hyL : y ∈ L := hy.1
  have hnK : (N ⟨y, hyL⟩ : Ω) ∈ i224K B L := by
    refine (iSup₂_le fun g hg => ?_ : (⨆ g ∈ R, L.map (MulAut.conj g).toMonoidHom) ≤ i224K B L)
      (hN1 ⟨y, hyL⟩)
    exact le_iSup₂_of_le (f := fun (b : Ω) (_ : b ∈ B) => i224Cj b L) g (hRB hg) le_rfl
  have hFB : F ≤ B := hFA.trans inf_le_left
  have hFR : F ⊓ R = ⊥ := by
    rw [eq_bot_iff, ← hRA]
    exact inf_le_inf_right _ hFA
  have hcFR := i224_card_sup (P := F) (Q := R)
    (fun x hx y hy => hBc x (hFB hx) y (hRB hy)) hFR
  have hnC : (N ⟨y, hyL⟩ : Ω) ∈ Subgroup.centralizer ((F ⊔ R : Subgroup Ω) : Set Ω) := by
    have hle : F ⊔ R ≤ Subgroup.centralizer ({(N ⟨y, hyL⟩ : Ω)} : Set Ω) := by
      refine sup_le (fun f hf => ?_) (fun r hr => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hfn : f ∈ Subgroup.normalizer (L : Set Ω) := (hFA hf).2
        have h1 := hN3 f hfn (fun g hg => hBc f (hFB hf) g (hRB hg)) ⟨y, hyL⟩
        have h2 : L.normalizerMonoidHom ⟨f, hfn⟩ ⟨y, hyL⟩ = ⟨y, hyL⟩ := by
          apply Subtype.ext
          show f * y * f⁻¹ = y
          have := Subgroup.mem_centralizer_iff.1 hy.2 f hf
          rw [this]; group
        rw [h2] at h1
        have : f * (N ⟨y, hyL⟩ : Ω) = (N ⟨y, hyL⟩ : Ω) * f := by
          calc f * (N ⟨y, hyL⟩ : Ω) = (f * (N ⟨y, hyL⟩ : Ω) * f⁻¹) * f := by group
            _ = _ := by rw [h1]
        exact this
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := hN2 r hr ⟨y, hyL⟩
        calc r * (N ⟨y, hyL⟩ : Ω) = (r * (N ⟨y, hyL⟩ : Ω) * r⁻¹) * r := by group
          _ = (N ⟨y, hyL⟩ : Ω) * r := by rw [h1]
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)
  refine ⟨N ⟨y, hyL⟩, ?_, fun g₀ hg₀ => ?_, fun Y hY y' hy' => hN5 Y hY ⟨y, hyL⟩ y' hy'⟩
  · refine Subgroup.mem_iSup_of_mem (F ⊔ R) (Subgroup.mem_iSup_of_mem ⟨sup_le hFB hRB, ?_⟩
      ⟨hnK, hnC⟩)
    rw [hcFR]
    exact hcard
  · obtain ⟨z, hz, hnz⟩ := hN4 g₀ hg₀ ⟨y, hyL⟩
    refine ⟨z, fun u hu => ?_, hnz⟩
    have h1 := hz (g₀⁻¹ * u * g₀) (mem_i224Cj.1 hu)
    have e : g₀ * (g₀⁻¹ * u * g₀) * g₀⁻¹ = u := by group
    rwa [e] at h1

end CFSG.HardMathSupport.Solomon.Coordinator
