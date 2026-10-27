module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Weak

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

variable {G : Type} [Group G] {L : Subgroup G} {z t : G} {T E : Subgroup G}

theorem OuterE.mem_sup_of_cent_z (h : OuterE G L z t T E) {S : Subgroup G}
    (hSC : S ≤ centralizer (E : Set G))
    (hcent : ∀ v ∈ centralizer (E : Set G), v * z = z * v → v = 1 ∨ v = z ∨ v = t ∨ v = t * z)
    {u : G} (hu : u ∈ S ⊔ E) (huz : u * z = z * u) : u ∈ E ⊔ zpowers z := by
  have hES : E ≤ centralizer (S : Set G) := fun e he =>
    mem_centralizer_iff.2 fun s hs => (mem_centralizer_iff.1 (hSC hs) e he).symm
  obtain ⟨s, hs, e, he, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hES hu
  have hez : e * z = z * e := h.cfg.z_comm_of_mem_A (h.E_le_L he)
  have hsz : s * z = z * s := by
    have h1 : s * z * e = z * s * e := by
      calc s * z * e = s * (z * e) := by group
        _ = s * (e * z) := by rw [hez]
        _ = (s * e) * z := by group
        _ = z * (s * e) := huz
        _ = z * s * e := by group
    exact mul_right_cancel h1
  have htE : t ∈ E := h.econfig.t_mem
  have hzmem : z ∈ E ⊔ zpowers z := mem_sup_right (mem_zpowers z)
  have hEle : E ≤ E ⊔ zpowers z := le_sup_left
  rcases hcent s (hSC hs) hsz with h1 | h1 | h1 | h1
  · rw [h1, one_mul]; exact hEle he
  · rw [h1]; exact mul_mem hzmem (hEle he)
  · rw [h1]; exact mul_mem (hEle htE) (hEle he)
  · rw [h1]; exact mul_mem (mul_mem (hEle htE) hzmem) (hEle he)

theorem OuterE.normalizes_of_cent_z (h : OuterE G L z t T E)
    (hzt : ∃ x : G, x * z * x⁻¹ = z * t) {S : Subgroup G}
    (hSC : S ≤ centralizer (E : Set G))
    (hcent : ∀ v ∈ centralizer (E : Set G), v * z = z * v → v = 1 ∨ v = z ∨ v = t ∨ v = t * z)
    {m : G} (hm : m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G)) (hmz : m * z * m⁻¹ = z) :
    m ∈ normalizer (E : Set G) := by
  have key : ∀ m : G, m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G) → m * z * m⁻¹ = z →
      ∀ e ∈ E, m * e * m⁻¹ ∈ E := by
    intro m hm hmz e he
    have hmz' : m * z = z * m := by
      calc m * z = (m * z * m⁻¹) * m := by group
        _ = z * m := by rw [hmz]
    have hmz'' : m⁻¹ * z = z * m⁻¹ := by
      calc m⁻¹ * z = m⁻¹ * (z * m) * m⁻¹ := by group
        _ = m⁻¹ * (m * z) * m⁻¹ := by rw [hmz']
        _ = z * m⁻¹ := by group
    have he' : e ∈ closure {e | e ∈ E ∧ e * e = 1 ∧ e ≠ 1} := h.econfig.gen ▸ he
    clear he
    induction he' using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨hxE, hx2, hx1⟩ := hx
      have hmx : m * x * m⁻¹ ∈ S ⊔ E := (mem_normalizer_iff.1 hm x).1 (mem_sup_right hxE)
      have hxz : x * z = z * x := h.cfg.z_comm_of_mem_A (h.E_le_L hxE)
      have hcomm : (m * x * m⁻¹) * z = z * (m * x * m⁻¹) := by
        calc m * x * m⁻¹ * z = m * x * (m⁻¹ * z) := by group
          _ = m * x * (z * m⁻¹) := by rw [hmz'']
          _ = m * (x * z) * m⁻¹ := by group
          _ = m * (z * x) * m⁻¹ := by rw [hxz]
          _ = (m * z) * x * m⁻¹ := by group
          _ = (z * m) * x * m⁻¹ := by rw [hmz']
          _ = z * (m * x * m⁻¹) := by group
      have hmxE := h.mem_sup_of_cent_z hSC hcent hmx hcomm
      obtain ⟨c, -, hc⟩ := h.econfig.conj x hxE hx2 hx1
      exact h.mem_of_conj_t hzt hmxE ⟨m * c, by rw [hc]; group⟩
    | one => simp
    | mul a b _ _ ha hb =>
      have : m * (a * b) * m⁻¹ = (m * a * m⁻¹) * (m * b * m⁻¹) := by group
      rw [this]; exact mul_mem ha hb
    | inv a _ ha =>
      have : m * a⁻¹ * m⁻¹ = (m * a * m⁻¹)⁻¹ := by group
      rw [this]; exact inv_mem ha
  rw [mem_normalizer_iff]
  intro e
  constructor
  · exact key m hm hmz e
  · intro hme
    have hinv : m⁻¹ * z * m⁻¹⁻¹ = z := by
      have hmz' : m * z = z * m := by
        calc m * z = (m * z * m⁻¹) * m := by group
          _ = z * m := by rw [hmz]
      calc m⁻¹ * z * m⁻¹⁻¹ = m⁻¹ * (z * m) := by group
        _ = m⁻¹ * (m * z) := by rw [hmz']
        _ = z := by group
    have := key m⁻¹ (inv_mem hm) hinv _ hme
    simpa [mul_assoc] using this

end CFSG.EvenSporadicStandard.Fin76b
