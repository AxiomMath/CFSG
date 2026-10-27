module

public import CFSG.GH74.GLS.C3.Layer1.P34Basic

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34

open Subgroup CFSG.GH74.GLS.Bg.Thompson CFSG.Quasithin

variable {X : Type} [Group X] [Finite X] {T P Q : Subgroup X} {x z f h : X}

theorem exists_conj_central_of_sylow (c : Cfg34 X T P Q x z f h) {y g' : X}
    (hy : g'⁻¹ * z * g' = y) :
    ∃ g : X, g⁻¹ * y * g = z ∧ ∀ w ∈ T ⊓ centralizer ({y} : Set X), g⁻¹ * w * g ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({z} : Set X) with hC
  have hTC : T ≤ C := fun t ht => mem_centralizer_singleton_iff.2 (c.z_cent_T t ht)
  have hzy : g' * y * g'⁻¹ = z := by rw [← hy]; group
  set K : Subgroup X := (T ⊓ centralizer ({y} : Set X)).map (MulAut.conj g').toMonoidHom with hK
  have hKC : K ≤ C := by
    rintro _ ⟨w, hw, rfl⟩
    rw [hC, mem_centralizer_singleton_iff]
    have hwy : w * y = y * w := mem_centralizer_singleton_iff.1 hw.2
    show (g' * w * g'⁻¹) * z = z * (g' * w * g'⁻¹)
    rw [← hzy]
    calc g' * w * g'⁻¹ * (g' * y * g'⁻¹) = g' * (w * y) * g'⁻¹ := by group
      _ = g' * (y * w) * g'⁻¹ := by rw [hwy]
      _ = g' * y * g'⁻¹ * (g' * w * g'⁻¹) := by group
  have hKp : IsPGroup 2 ↥K := (c.T_pgroup.to_le (inf_le_left : T ⊓ centralizer ({y} : Set X) ≤ T)).map _
  have hidx : ¬ 2 ∣ T.relIndex C := fun h2 =>
    c.T_index (h2.trans (Subgroup.relIndex_dvd_index_of_le hTC))
  obtain ⟨c₀, hc₀C, hc₀⟩ := exists_conj_into_sylow hKC hKp hTC c.T_pgroup hidx
  have hc₀z : c₀ * z = z * c₀ := mem_centralizer_singleton_iff.1 hc₀C
  refine ⟨g'⁻¹ * c₀, ?_, fun w hw => ?_⟩
  · calc (g'⁻¹ * c₀)⁻¹ * y * (g'⁻¹ * c₀) = c₀⁻¹ * (g' * y * g'⁻¹) * c₀ := by group
      _ = c₀⁻¹ * z * c₀ := by rw [hzy]
      _ = z := by
        calc c₀⁻¹ * z * c₀ = c₀⁻¹ * (z * c₀) := by group
          _ = c₀⁻¹ * (c₀ * z) := by rw [hc₀z]
          _ = z := by group
  · have := hc₀ (g' * w * g'⁻¹) ⟨w, hw, rfl⟩
    have e : (g'⁻¹ * c₀)⁻¹ * w * (g'⁻¹ * c₀) = c₀⁻¹ * (g' * w * g'⁻¹) * c₀ := by group
    rw [e]
    exact this

theorem zconj_cent_eq (c : Cfg34 X T P Q x z f h) (h38 : Lemma38 T P z) {y : X}
    (hyc : ∃ g' : X, g'⁻¹ * z * g' = y) (hyP : ∀ a ∈ P, y * a = a * y) : y = z := by
  obtain ⟨g', hg'⟩ := hyc
  obtain ⟨g, hg, hgT⟩ := exists_conj_central_of_sylow c hg'
  have hPT : ∀ a ∈ P, g⁻¹ * a * g ∈ T := fun a ha =>
    hgT a ⟨c.P_le ha, mem_centralizer_singleton_iff.2 (hyP a ha).symm⟩
  have hz := h38 g hPT
  calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    _ = g * z * g⁻¹ := by rw [hg]
    _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hz]
    _ = z := by group

theorem lemma39 (c : Cfg34 X T P Q x z f h) (h38 : Lemma38 T P z) : Lemma39 T P Q z f := by
  intro y hyc hyT hyR
  by_contra hyP
  obtain ⟨g', hg'⟩ := hyc
  have hy2 : y * y = 1 := by
    rw [← hg']
    calc g'⁻¹ * z * g' * (g'⁻¹ * z * g') = g'⁻¹ * (z * z) * g' := by group
      _ = 1 := by rw [c.z_sq]; group
  obtain ⟨g, hgC, hgmem⟩ := c.kf_C y hyT hy2 hyR hyP
  have hgT : g⁻¹ * y * g ∈ T := by
    have : (Q ⊔ zpowers f) ⊔ zpowers z ≤ T :=
      sup_le (sup_le c.Q_le (zpowers_le.2 c.f_mem)) (zpowers_le.2 c.z_mem_T)
    exact this hgmem
  have hcent : ∀ a ∈ P, (g⁻¹ * y * g) * a = a * (g⁻¹ * y * g) := (c.kf_3B _ hgT).2 hgmem
  have hconj : ∃ g'' : X, g''⁻¹ * z * g'' = g⁻¹ * y * g :=
    ⟨g' * g, by rw [← hg']; group⟩
  have heq := zconj_cent_eq c h38 hconj hcent
  have hg_inv : g⁻¹ ∈ centralizer ({x} : Set X) := (centralizer ({x} : Set X)).inv_mem hgC
  have hyg : y = (g⁻¹)⁻¹ * z * g⁻¹ := by
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [heq]
      _ = (g⁻¹)⁻¹ * z * g⁻¹ := by simp
  have := c.kf_zC g⁻¹ hg_inv (by rw [← hyg]; exact hyT)
  exact hyP (by rw [← hyg] at this; exact this)

end CFSG.GH74.GLS.C3.Layer1.P34
