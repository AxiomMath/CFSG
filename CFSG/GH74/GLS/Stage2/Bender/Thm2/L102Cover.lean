module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L102Res
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L102Cop

public section

open Subgroup
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L102

section Conj

variable {G : Type*} [Group G]

private theorem mem_map_conj_iff {V : Subgroup G} {g x : G} :
    x ∈ V.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ V := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

private theorem map_conj_le_of_mem_normalizer {O V : Subgroup G} {g : G}
    (hg : g ∈ normalizer (O : Set G)) (hVO : V ≤ O) :
    V.map (MulAut.conj g).toMonoidHom ≤ O := by
  intro x hx
  rw [mem_map_conj_iff] at hx
  exact (mem_normalizer_iff''.mp hg x).mpr (hVO hx)

private theorem maximal_map_conj {p : ℕ} {O V : Subgroup G} {g : G}
    (hg : g ∈ normalizer (O : Set G))
    (hVmax : ∀ W : Subgroup G, W ≤ O → IsPGroup p W → V ≤ W → W = V) :
    ∀ W : Subgroup G, W ≤ O → IsPGroup p W → V.map (MulAut.conj g).toMonoidHom ≤ W →
      W = V.map (MulAut.conj g).toMonoidHom := by
  intro W hWO hWp hVW
  have hW'O : W.map (MulAut.conj g⁻¹).toMonoidHom ≤ O :=
    map_conj_le_of_mem_normalizer (inv_mem hg) hWO
  have hW'p : IsPGroup p (W.map (MulAut.conj g⁻¹).toMonoidHom) := hWp.map _
  have hVW' : V ≤ W.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro v hv
    rw [mem_map_conj_iff]
    have e : g⁻¹ * (g * v * g⁻¹) * g = v := by group
    have : g * v * g⁻¹ ∈ V.map (MulAut.conj g).toMonoidHom := by
      rw [mem_map_conj_iff, e]
      exact hv
    simpa using hVW this
  have h := hVmax _ hW'O hW'p hVW'
  ext x
  rw [mem_map_conj_iff]
  have h2 : g⁻¹ * x * g ∈ W.map (MulAut.conj g⁻¹).toMonoidHom ↔ g⁻¹ * x * g ∈ V := by
    rw [h]
  rw [← h2, mem_map_conj_iff]
  simp [mul_assoc]

end Conj

section Cover

variable {G : Type*} [Group G] [Finite G]

theorem frattini_fixed_points {p : ℕ} (hp : p.Prime) {X O V U : Subgroup G}
    (hU2 : IsPGroup 2 U) (hUO : U ≤ normalizer (O : Set G))
    (hOX : O ≤ X) (hXO : X ≤ normalizer (O : Set G)) (hOodd : Odd (Nat.card O))
    (hVO : V ≤ O) (hVp : IsPGroup p V)
    (hVmax : ∀ W : Subgroup G, W ≤ O → IsPGroup p W → V ≤ W → W = V)
    (hUV : U ≤ normalizer (V : Set G)) {w : G} (hw : w ∈ X ⊓ centralizer (U : Set G)) :
    ∃ c ∈ O ⊓ centralizer (U : Set G),
      ∃ n ∈ X ⊓ centralizer (U : Set G) ⊓ normalizer (V : Set G), w = c * n := by
  have hwX : w ∈ X := hw.1
  have hwU : w ∈ centralizer (U : Set G) := hw.2
  have hwO : w ∈ normalizer (O : Set G) := hXO hwX
  have hUV' : U ≤ normalizer ((V.map (MulAut.conj w).toMonoidHom : Subgroup G) : Set G) := by
    intro u hu
    have hc : Commute u w := mem_centralizer_iff.mp hwU u hu
    rw [mem_normalizer_iff]
    intro h
    rw [mem_map_conj_iff, mem_map_conj_iff]
    have e : w⁻¹ * (u * h * u⁻¹) * w = u * (w⁻¹ * h * w) * u⁻¹ := by
      calc w⁻¹ * (u * h * u⁻¹) * w = (w⁻¹ * u) * h * (u⁻¹ * w) := by group
        _ = (u * w⁻¹) * h * (w * u⁻¹) := by
          rw [← hc.inv_right.eq, ← hc.inv_left.eq]
        _ = u * (w⁻¹ * h * w) * u⁻¹ := by group
    rw [e]
    exact mem_normalizer_iff.mp (hUV hu) (w⁻¹ * h * w)
  obtain ⟨c, hc, hcV⟩ := exists_centralizer_conj hp hOodd hU2 hUO hVO hVp hVmax hUV
    (map_conj_le_of_mem_normalizer hwO hVO) (hVp.map _) (maximal_map_conj hwO hVmax) hUV'
  have hcW : c ∈ X ⊓ centralizer (U : Set G) := ⟨hOX hc.1, hc.2⟩
  have hnW : c⁻¹ * w ∈ X ⊓ centralizer (U : Set G) := mul_mem (inv_mem hcW) hw
  have hnV : c⁻¹ * w ∈ normalizer (V : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    have e : c⁻¹ * w * h * (c⁻¹ * w)⁻¹ = c⁻¹ * (w * h * w⁻¹) * c := by group
    rw [e, ← hcV, mem_map_conj_iff]
    have e2 : w⁻¹ * (w * h * w⁻¹) * w = h := by group
    rw [e2]
  exact ⟨c, hc, c⁻¹ * w, Subgroup.mem_inf.mpr ⟨hnW, hnV⟩, by simp⟩

theorem cover_normalizer {p : ℕ} (hp : p.Prime) {X O V U I I₁ K : Subgroup G}
    (hU2 : IsPGroup 2 U) (hUO : U ≤ normalizer (O : Set G))
    (hOX : O ≤ X) (hXO : X ≤ normalizer (O : Set G)) (hOodd : Odd (Nat.card O))
    (hVO : V ≤ O) (hVp : IsPGroup p V)
    (hVmax : ∀ W : Subgroup G, W ≤ O → IsPGroup p W → V ≤ W → W = V)
    (hUV : U ≤ normalizer (V : Set G))
    (hI₁X : I₁ ≤ X) (hI₁U : I₁ ≤ centralizer (U : Set G)) (hI₁perf : ⁅I₁, I₁⁆ = I₁)
    (hXdec : ∀ w ∈ X ⊓ centralizer (U : Set G),
      ∃ m ∈ O ⊓ centralizer (U : Set G), ∃ i ∈ I₁, w = m * i)
    (hI₁I : I₁ ≤ I) (hCI : ∀ c ∈ centralizer (U : Set G), c ∈ normalizer (I : Set G))
    (hKI : K ≤ I) (hKn : I ≤ normalizer (K : Set G)) (hKodd : Odd (Nat.card K))
    (hKmax : ∀ L : Subgroup G, L ≤ I → I ≤ normalizer (L : Set G) → Odd (Nat.card L) → L ≤ K)
    (hcov : I ≤ I₁ ⊔ K) :
    I ≤ (X ⊓ normalizer (V : Set G) ⊓ I) ⊔ K := by
  set W : Subgroup G := X ⊓ centralizer (U : Set G) with hW
  set K₀ : Subgroup G := O ⊓ centralizer (U : Set G) with hK₀
  set Z : Subgroup G := W ⊓ normalizer (V : Set G) with hZ
  have hZW : Z ≤ W := inf_le_left
  have hK₀W : K₀ ≤ W := inf_le_inf_right _ hOX
  have hWK₀ : W ≤ normalizer (K₀ : Set G) := by
    intro w hw
    have hw' := Subgroup.mem_inf.mp hw
    exact inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨hXO hw'.1, le_normalizer hw'.2⟩)
  have hWcov : W ≤ K₀ ⊔ Z := by
    intro w hw
    obtain ⟨c, hc, n, hn, rfl⟩ := frattini_fixed_points hp hU2 hUO hOX hXO hOodd hVO hVp hVmax hUV hw
    exact Subgroup.mul_mem_sup hc hn
  have hdW : dres W ≤ dres Z ⊔ K₀ := dres_le_sup_of_covering hZW hK₀W hWK₀ hWcov
  have hI₁W : I₁ ≤ W := le_inf hI₁X hI₁U
  have hI₁dW : I₁ ≤ dres W := le_dres_of_perfect hI₁perf hI₁W
  have hK₀odd : Odd (Nat.card K₀) := hOodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hK₀I : K₀ ≤ normalizer (I : Set G) := fun c hc => hCI c (Subgroup.mem_inf.mp hc).2
  have hWIK₀ : dres Z ≤ I ⊔ K₀ := by
    intro w hw
    have hwW : w ∈ W := hZW (dres_le Z hw)
    obtain ⟨m, hm, i, hi, rfl⟩ := hXdec w hwW
    rw [sup_comm]
    exact Subgroup.mul_mem_sup hm (hI₁I hi)
  have hdZI : dres Z ≤ I := perfect_le_of_le_sup_odd (dres_perfect Z) hK₀odd hK₀I hWIK₀
  have hdZn : dres Z ≤ normalizer (K₀ : Set G) := (dres_le Z).trans (hZW.trans hWK₀)
  have h5 : ∀ i ∈ I₁, ∃ d ∈ dres Z, d⁻¹ * i ∈ K₀ ⊓ I := by
    intro i hi
    have hi' : i ∈ K₀ ⊔ dres Z := by
      rw [sup_comm]
      exact hdW (hI₁dW hi)
    obtain ⟨d, hd, hκ⟩ := exists_mem_inv_mul_mem hdZn hi'
    exact ⟨d, hd, Subgroup.mem_inf.mpr ⟨hκ, mul_mem (inv_mem (hdZI hd)) (hI₁I hi)⟩⟩
  have hK₀IK : K₀ ⊓ I ≤ K := by
    have hA : Odd (Nat.card (K₀ ⊓ I : Subgroup G)) :=
      hK₀odd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    have hL : (K₀ ⊓ I) ⊔ K ≤ K := by
      refine hKmax _ (sup_le inf_le_right hKI)
        (hcov.trans (sup_le ?_ ?_))
        (odd_card_sup_of_normalizes hA hKodd (inf_le_right.trans hKn))
      · intro x hx
        have h1 : x ∈ normalizer ((K₀ ⊓ I : Subgroup G) : Set G) :=
          inf_normalizer_le_normalizer_inf
            (Subgroup.mem_inf.mpr ⟨hWK₀ (hI₁W hx), le_normalizer (hI₁I hx)⟩)
        exact inf_normalizer_le_normalizer_sup _ _
          (Subgroup.mem_inf.mpr ⟨h1, hKn (hI₁I hx)⟩)
      · exact le_sup_right.trans le_normalizer
    exact le_sup_left.trans hL
  have hI₁fin : I₁ ≤ (X ⊓ normalizer (V : Set G) ⊓ I) ⊔ K := by
    intro i hi
    obtain ⟨d, hd, hκ⟩ := h5 i hi
    have hdZ : d ∈ Z := dres_le Z hd
    have hdZ' := Subgroup.mem_inf.mp hdZ
    have hdX : d ∈ X := (Subgroup.mem_inf.mp hdZ'.1).1
    have hdmem : d ∈ X ⊓ normalizer (V : Set G) ⊓ I :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hdX, hdZ'.2⟩, hdZI hd⟩
    have hi_eq : i = d * (d⁻¹ * i) := by simp
    rw [hi_eq]
    exact Subgroup.mul_mem_sup hdmem (hK₀IK hκ)
  exact hcov.trans (sup_le hI₁fin le_sup_right)

end Cover

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L102
