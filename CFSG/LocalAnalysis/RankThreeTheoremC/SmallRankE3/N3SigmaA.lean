module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Q8D8

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG.ClassicalInvolution.Q3.Sec13

variable {Γ : Type} [Group Γ]

theorem commutator_mul_central {Zc : Subgroup Γ} (hZc : ∀ k ∈ Zc, ∀ g : Γ, g * k = k * g)
    {x y c d : Γ} (hc : c ∈ Zc) (hd : d ∈ Zc) :
    x * c * (y * d) * (x * c)⁻¹ * (y * d)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  have h1 : ∀ w, w * c = c * w := fun w => hZc c hc w
  have h2 : ∀ w, w * d = d * w := fun w => hZc d hd w
  have hP : x * c * (y * d) = x * y * (c * d) := by
    calc x * c * (y * d) = x * (c * y) * d := by group
      _ = x * (y * c) * d := by rw [← h1 y]
      _ = x * y * (c * d) := by group
  have hQ : y * d * (x * c) = y * x * (c * d) := by
    calc y * d * (x * c) = y * (d * x) * c := by group
      _ = y * (x * d) * c := by rw [← h2 x]
      _ = y * x * (d * c) := by group
      _ = y * x * (c * d) := by rw [h1 d]
  calc x * c * (y * d) * (x * c)⁻¹ * (y * d)⁻¹
      = x * c * (y * d) * (y * d * (x * c))⁻¹ := by group
    _ = x * y * (c * d) * (y * x * (c * d))⁻¹ := by rw [hP, hQ]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem exists_actsAs {S : Subgroup Γ} {z : Γ} {Zc : Subgroup Γ}
    {Ψ : ↥S →* Multiplicative Sp4.V4}
    (hS : Q8D8Facts S z) (hΨ : PsiSpec S z Ψ) (hZc : ∀ k ∈ Zc, ∀ g : Γ, g * k = k * g)
    (hz : z ∈ Zc) {g : Γ} (hg : g ∈ Subgroup.normalizer ((S ⊔ Zc : Subgroup Γ) : Set Γ)) :
    ∃ φ : Sp4.V4 ≃+ Sp4.V4, ActsAs S Zc Ψ g φ ∧
      ∀ x y, Sp4.symp (φ x) (φ y) = Sp4.symp x y := by
  have hZn : Zc.Normal := ⟨fun n hn h => by rw [hZc n hn h, mul_inv_cancel_right]; exact hn⟩
  have hA : ∀ u : S, (u : Γ) ∈ Zc → Ψ u = 1 := by
    intro u hu
    rw [hΨ.ker_iff u]
    refine (hS.center_iff (u : Γ) u.2).mp ?_
    intro s' _
    exact (hZc _ hu s').symm
  have hB : ∀ a b : S, ∀ k k' : Γ, k ∈ Zc → k' ∈ Zc →
      (a : Γ) * k = (b : Γ) * k' → Ψ a = Ψ b := by
    intro a b k k' hk hk' h
    have huZ : ((a⁻¹ * b : S) : Γ) ∈ Zc := by
      have e : ((a⁻¹ * b : S) : Γ) = k * k'⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        calc (a : Γ)⁻¹ * (b : Γ) = (a : Γ)⁻¹ * ((b : Γ) * k') * k'⁻¹ := by group
          _ = (a : Γ)⁻¹ * ((a : Γ) * k) * k'⁻¹ := by rw [h]
          _ = k * k'⁻¹ := by group
      rw [e]
      exact Zc.mul_mem hk (Zc.inv_mem hk')
    have h1 := hA _ huZ
    rw [map_mul, map_inv] at h1
    exact inv_mul_eq_one.mp h1
  have hdec : ∀ s : S, ∃ s' : S, ∃ c : Γ, c ∈ Zc ∧ g * (s : Γ) * g⁻¹ = (s' : Γ) * c := by
    intro s
    have hmem : g * (s : Γ) * g⁻¹ ∈ (S ⊔ Zc : Subgroup Γ) := by
      have hs : (s : Γ) ∈ (S ⊔ Zc : Subgroup Γ) := Subgroup.mem_sup_left s.2
      exact (Subgroup.mem_set_normalizer_iff.mp hg _).mp hs
    obtain ⟨y, hy, c, hc, hyc⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
    exact ⟨⟨y, hy⟩, c, hc, hyc.symm⟩
  choose f cz hcz hfc using hdec
  have hT : ∀ s t : S, Ψ s = Ψ t → Ψ (f s) = Ψ (f t) := by
    intro s t hst
    obtain ⟨u, rfl⟩ : ∃ u : S, t = s * u := ⟨s⁻¹ * t, (mul_inv_cancel_left s t).symm⟩
    have hu1 : Ψ u = 1 := by simpa [map_mul] using hst
    have huZ : (u : Γ) ∈ Zc := by
      rcases (hΨ.ker_iff u).mp hu1 with h | h <;> rw [h]
      · exact Zc.one_mem
      · exact hz
    have hgu : g * (u : Γ) * g⁻¹ = (u : Γ) := by
      rw [hZc _ huZ g, mul_inv_cancel_right]
    have hgt : g * ((s * u : S) : Γ) * g⁻¹ = (f s : Γ) * (cz s * (u : Γ)) := by
      rw [Subgroup.coe_mul,
        show g * ((s : Γ) * (u : Γ)) * g⁻¹ = (g * (s : Γ) * g⁻¹) * (g * (u : Γ) * g⁻¹) by group,
        hfc s, hgu, mul_assoc]
    exact hB (f s) (f (s * u)) (cz s * (u : Γ)) (cz (s * u)) (Zc.mul_mem (hcz s) huZ) (hcz _)
      (hgt.symm.trans (hfc (s * u)))
  have hM : ∀ s t : S, Ψ (f (s * t)) = Ψ (f s) * Ψ (f t) := by
    intro s t
    rw [← map_mul]
    refine hB (f (s * t)) (f s * f t) (cz (s * t)) (cz s * cz t) (hcz _)
      (Zc.mul_mem (hcz s) (hcz t)) ?_
    have hcomm : cz s * (f t : Γ) = (f t : Γ) * cz s := (hZc (cz s) (hcz s) (f t)).symm
    rw [Subgroup.coe_mul, ← hfc (s * t), Subgroup.coe_mul,
      show g * ((s : Γ) * (t : Γ)) * g⁻¹ = (g * (s : Γ) * g⁻¹) * (g * (t : Γ) * g⁻¹) by group,
      hfc s, hfc t]
    calc (f s : Γ) * cz s * ((f t : Γ) * cz t)
        = (f s : Γ) * (cz s * (f t : Γ)) * cz t := by group
      _ = (f s : Γ) * ((f t : Γ) * cz s) * cz t := by rw [hcomm]
      _ = (f s : Γ) * (f t : Γ) * (cz s * cz t) := by group
  choose σ hσ using (hΨ.surj : ∀ b, ∃ a, Ψ a = b)
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : Sp4.V4 → Sp4.V4,
      ∀ s : S, φ₀ (Multiplicative.toAdd (Ψ s)) = Multiplicative.toAdd (Ψ (f s)) := by
    refine ⟨fun w => Multiplicative.toAdd (Ψ (f (σ (Multiplicative.ofAdd w)))), fun s => ?_⟩
    have hs : Ψ (σ (Multiplicative.ofAdd (Multiplicative.toAdd (Ψ s)))) = Ψ s :=
      (hσ _).trans rfl
    show Multiplicative.toAdd (Ψ (f (σ (Multiplicative.ofAdd (Multiplicative.toAdd (Ψ s)))))) = _
    rw [hT _ _ hs]
  have hta : ∀ a b : Multiplicative Sp4.V4,
      Multiplicative.toAdd (a * b) = Multiplicative.toAdd a + Multiplicative.toAdd b :=
    fun _ _ => rfl
  have hsurjV : ∀ w : Sp4.V4, ∃ s : S, Multiplicative.toAdd (Ψ s) = w := by
    intro w
    obtain ⟨s, hs⟩ := hΨ.surj (Multiplicative.ofAdd w)
    exact ⟨s, congrArg Multiplicative.toAdd hs⟩
  have hadd : ∀ w₁ w₂ : Sp4.V4, φ₀ (w₁ + w₂) = φ₀ w₁ + φ₀ w₂ := by
    intro w₁ w₂
    obtain ⟨s, rfl⟩ := hsurjV w₁
    obtain ⟨t, rfl⟩ := hsurjV w₂
    have e1 : Multiplicative.toAdd (Ψ s) + Multiplicative.toAdd (Ψ t)
        = Multiplicative.toAdd (Ψ (s * t)) := by
      rw [map_mul, hta]
    rw [e1, hφ₀ (s * t), hφ₀ s, hφ₀ t, ← hta, hM s t]
  obtain ⟨φh, hφh⟩ : ∃ φh : Sp4.V4 →+ Sp4.V4, ∀ w, φh w = φ₀ w :=
    ⟨AddMonoidHom.mk' φ₀ hadd, fun _ => rfl⟩
  have hinj : Function.Injective φh := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨s, rfl⟩ := hsurjV w
    rw [hφh, hφ₀] at hw
    have hfs : Ψ (f s) = 1 := Multiplicative.toAdd.injective (hw.trans rfl)
    have hfsZ : (f s : Γ) ∈ Zc := by
      rcases (hΨ.ker_iff (f s)).mp hfs with h | h <;> rw [h]
      · exact Zc.one_mem
      · exact hz
    have hm : g * (s : Γ) * g⁻¹ ∈ Zc := by
      rw [hfc s]
      exact Zc.mul_mem hfsZ (hcz s)
    have hsZ : (s : Γ) ∈ Zc := by
      have h2 : (s : Γ) = g * (s : Γ) * g⁻¹ := by
        calc (s : Γ) = g⁻¹ * (g * (s : Γ) * g⁻¹) * g := by group
          _ = (g * (s : Γ) * g⁻¹) * g⁻¹ * g := by rw [hZc _ hm g⁻¹]
          _ = g * (s : Γ) * g⁻¹ := by group
      rw [h2]
      exact hm
    simp [hA s hsZ]
  have hbij : Function.Bijective φh := Finite.injective_iff_bijective.mp hinj
  obtain ⟨e, he⟩ : ∃ e : Sp4.V4 ≃+ Sp4.V4, ∀ w, e w = φh w :=
    ⟨AddEquiv.ofBijective φh hbij, fun _ => rfl⟩
  have hact : ∀ (s s' : S) (k : Γ), k ∈ Zc → g * (s : Γ) * g⁻¹ = (s' : Γ) * k →
      e (Multiplicative.toAdd (Ψ s)) = Multiplicative.toAdd (Ψ s') := by
    intro s s' k hk h
    rw [he, hφh, hφ₀]
    exact congrArg Multiplicative.toAdd
      (hB (f s) s' (cz s) k (hcz s) hk ((hfc s).symm.trans h))
  have hCD : ∀ s t : S, g * ((s : Γ) * (t : Γ) * (s : Γ)⁻¹ * (t : Γ)⁻¹) * g⁻¹ =
      (f s : Γ) * (f t : Γ) * (f s : Γ)⁻¹ * (f t : Γ)⁻¹ := by
    intro s t
    rw [show g * ((s : Γ) * (t : Γ) * (s : Γ)⁻¹ * (t : Γ)⁻¹) * g⁻¹ =
        (g * (s : Γ) * g⁻¹) * (g * (t : Γ) * g⁻¹) * (g * (s : Γ) * g⁻¹)⁻¹
          * (g * (t : Γ) * g⁻¹)⁻¹ by group,
      hfc s, hfc t]
    exact commutator_mul_central hZc (hcz s) (hcz t)
  have hconj1 : ∀ C : Γ, g * C * g⁻¹ = 1 ↔ C = 1 := by
    intro C
    constructor
    · intro h
      calc C = g⁻¹ * (g * C * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · intro h
      rw [h]
      group
  have hsymm : ∀ s t : S, ((f s : Γ) * (f t : Γ) * (f s : Γ)⁻¹ * (f t : Γ)⁻¹ = 1 ↔
      (s : Γ) * (t : Γ) * (s : Γ)⁻¹ * (t : Γ)⁻¹ = 1) := by
    intro s t
    rw [← hCD s t]
    exact hconj1 _
  refine ⟨e, hact, ?_⟩
  intro x y
  obtain ⟨s, rfl⟩ := hsurjV x
  obtain ⟨t, rfl⟩ := hsurjV y
  rw [he, he, hφh, hφh, hφ₀, hφ₀, hΨ.form (f s) (f t), hΨ.form s t]
  by_cases h : (s : Γ) * (t : Γ) * (s : Γ)⁻¹ * (t : Γ)⁻¹ = 1
  · rw [if_pos h, if_pos ((hsymm s t).mpr h)]
  · rw [if_neg h, if_neg (fun h' => h ((hsymm s t).mp h'))]

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
