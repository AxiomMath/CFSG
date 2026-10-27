module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129W
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129W2

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129W

section Kstar

variable {Y : Type*} [Group Y]

private theorem iSup_le_centralizer {p : ℕ} {K : Subgroup Y} {a : Y}
    (hcomm : ∀ i j : Fin p, i ≠ j → ∀ x ∈ kconj a K i, ∀ y ∈ kconj a K j, x * y = y * x)
    (S : Finset (Fin p)) {j : Fin p} (hj : j ∉ S) :
    ∀ f ∈ (⨆ i ∈ S, kconj a K i : Subgroup Y), ∀ x ∈ kconj a K j, f * x = x * f := by
  have hle : (⨆ i ∈ S, kconj a K i : Subgroup Y) ≤ Subgroup.centralizer (kconj a K j : Set Y) := by
    refine iSup₂_le fun i hi x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    exact (hcomm i j hij x hx y hy).symm
  intro f hf x hx
  exact (Subgroup.mem_centralizer_iff.1 (hle hf) x hx).symm

private theorem act_kconj {a : Y} {K : Subgroup Y} {g k : Y} (hga : g * a = a * g)
    (hgk : ∀ y ∈ K, g * y * g⁻¹ = k * y * k⁻¹) (i : ℕ) {x : Y} (hx : x ∈ kconj a K i) :
    g * x * g⁻¹ = (a ^ i * k * (a ^ i)⁻¹) * x * (a ^ i * k * (a ^ i)⁻¹)⁻¹ := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  have hgi : g * a ^ i = a ^ i * g := (Commute.pow_right (show Commute g a from hga) i).eq
  have e1 : (a ^ i)⁻¹ * g⁻¹ = g⁻¹ * (a ^ i)⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, hgi]
  have h1 := hgk y hy
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * (a ^ i * y * (a ^ i)⁻¹) * g⁻¹
      = (g * a ^ i) * y * ((a ^ i)⁻¹ * g⁻¹) := by group
    _ = (a ^ i * g) * y * (g⁻¹ * (a ^ i)⁻¹) := by rw [hgi, e1]
    _ = a ^ i * (g * y * g⁻¹) * (a ^ i)⁻¹ := by group
    _ = (a ^ i * k * (a ^ i)⁻¹) * (a ^ i * y * (a ^ i)⁻¹) * (a ^ i * k * (a ^ i)⁻¹)⁻¹ := by
      rw [h1]; group

theorem mem_kstar_of_inner {p : ℕ} (K : Subgroup Y) (a : Y)
    (hcomm : ∀ i j : Fin p, i ≠ j → ∀ x ∈ kconj a K i, ∀ y ∈ kconj a K j, x * y = y * x)
    (hC : Subgroup.centralizer ((kstar p a K : Subgroup Y) : Set Y) = ⊥)
    {g : Y} (hga : g * a = a * g) {k : Y} (hk : k ∈ K)
    (hgk : ∀ y ∈ K, g * y * g⁻¹ = k * y * k⁻¹) : g ∈ kstar p a K := by
  classical
  have hcj : ∀ i : ℕ, a ^ i * k * (a ^ i)⁻¹ ∈ kconj a K i := fun i =>
    Subgroup.mem_map.2 ⟨k, hk, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  have key : ∀ S : Finset (Fin p), ∃ f ∈ (⨆ i ∈ S, kconj a K i : Subgroup Y),
      ∀ i ∈ S, ∀ x ∈ kconj a K i, f * x * f⁻¹ = g * x * g⁻¹ := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, Subgroup.one_mem _, by simp⟩
    | insert j S hj ih =>
      obtain ⟨f₀, hf₀, hf₀x⟩ := ih
      have hmono : (⨆ i ∈ S, kconj a K i : Subgroup Y) ≤ ⨆ i ∈ insert j S, kconj a K i :=
        iSup₂_le fun i hi => le_iSup₂_of_le i (Finset.mem_insert_of_mem hi) le_rfl
      have hjle : kconj a K j ≤ (⨆ i ∈ insert j S, kconj a K i : Subgroup Y) :=
        le_iSup₂_of_le j (Finset.mem_insert_self j S) le_rfl
      refine ⟨f₀ * (a ^ (j : ℕ) * k * (a ^ (j : ℕ))⁻¹), Subgroup.mul_mem _ (hmono hf₀)
        (hjle (hcj j)), ?_⟩
      intro i hi x hx
      rcases Finset.mem_insert.1 hi with rfl | hiS
      ·
        have hcx : f₀ * x = x * f₀ := iSup_le_centralizer hcomm S hj f₀ hf₀ x hx
        have hmem : (a ^ (i : ℕ) * k * (a ^ (i : ℕ))⁻¹) * x * (a ^ (i : ℕ) * k * (a ^ (i : ℕ))⁻¹)⁻¹ ∈
            kconj a K i := by
          have hc := hcj i
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hx) (Subgroup.inv_mem _ hc)
        have hcx' : f₀ * ((a ^ (i : ℕ) * k * (a ^ (i : ℕ))⁻¹) * x *
            (a ^ (i : ℕ) * k * (a ^ (i : ℕ))⁻¹)⁻¹) =
            ((a ^ (i : ℕ) * k * (a ^ (i : ℕ))⁻¹) * x * (a ^ (i : ℕ) * k * (a ^ (i : ℕ))⁻¹)⁻¹) * f₀ :=
          iSup_le_centralizer hcomm S hj f₀ hf₀ _ hmem
        calc f₀ * (a ^ (i : ℕ) * k * (a ^ (i : ℕ))⁻¹) * x * (f₀ * (a ^ (i : ℕ) * k * (a ^ (i : ℕ))⁻¹))⁻¹
            = f₀ * ((a ^ (i : ℕ) * k * (a ^ (i : ℕ))⁻¹) * x * (a ^ (i : ℕ) * k * (a ^ (i : ℕ))⁻¹)⁻¹) *
                f₀⁻¹ := by group
          _ = ((a ^ (i : ℕ) * k * (a ^ (i : ℕ))⁻¹) * x * (a ^ (i : ℕ) * k * (a ^ (i : ℕ))⁻¹)⁻¹) := by
            rw [hcx']; group
          _ = g * x * g⁻¹ := (act_kconj hga hgk i hx).symm
      ·
        have hij : j ≠ i := fun h => hj (h ▸ hiS)
        have hcx : (a ^ (j : ℕ) * k * (a ^ (j : ℕ))⁻¹) * x = x * (a ^ (j : ℕ) * k * (a ^ (j : ℕ))⁻¹) :=
          hcomm j i hij _ (hcj j) x hx
        calc f₀ * (a ^ (j : ℕ) * k * (a ^ (j : ℕ))⁻¹) * x * (f₀ * (a ^ (j : ℕ) * k * (a ^ (j : ℕ))⁻¹))⁻¹
            = f₀ * ((a ^ (j : ℕ) * k * (a ^ (j : ℕ))⁻¹) * x) * (a ^ (j : ℕ) * k * (a ^ (j : ℕ))⁻¹)⁻¹ *
                f₀⁻¹ := by group
          _ = f₀ * x * f₀⁻¹ := by rw [hcx]; group
          _ = g * x * g⁻¹ := hf₀x i hiS x hx
  obtain ⟨f, hf, hfx⟩ := key Finset.univ
  have hf' : f ∈ kstar p a K := by
    have : (⨆ i ∈ (Finset.univ : Finset (Fin p)), kconj a K i : Subgroup Y) = kstar p a K := by
      simp [kstar]
    rwa [this] at hf
  have hz : f⁻¹ * g ∈ Subgroup.centralizer ((kstar p a K : Subgroup Y) : Set Y) := by
    have hle : kstar p a K ≤ Subgroup.centralizer ({f⁻¹ * g} : Set Y) := by
      refine iSup_le fun i x hx => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hfx i (Finset.mem_univ i) x hx
      calc x * (f⁻¹ * g) = f⁻¹ * (f * x * f⁻¹) * g := by group
        _ = f⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
        _ = (f⁻¹ * g) * x := by group
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)
  rw [hC, Subgroup.mem_bot] at hz
  rw [← inv_mul_eq_one.1 hz]
  exact hf'

end Kstar

section Implementers

variable {Y : Type*} [Group Y]

open CFSG.Open

theorem exists_centralizing_pair {p : ℕ} (K F : Subgroup Y) (a : Y)
    (hcenter : ∀ z ∈ K, (∀ y ∈ K, z * y = y * z) → z = 1)
    (hcomm01 : ∀ x ∈ K, ∀ y ∈ kconj a K 1, x * y = y * x)
    (hFa : ∀ f ∈ F, f * a = a * f) (hFel : IsElemAbelian p F)
    (hFinner : ∀ f ∈ F, ∃ k ∈ K, ∀ y ∈ K, f * y * f⁻¹ = k * y * k⁻¹)
    (hFfaith : ∀ f ∈ F, (∀ y ∈ K, f * y = y * f) → f = 1) :
    ∃ X : Subgroup Y, IsElemAbelian p X ∧ Nat.card X = Nat.card F ∧
      (∀ x ∈ X, ∀ y ∈ K, x * y = y * x) ∧ (∀ x ∈ X, ∀ f ∈ F, x * f = f * x) := by
  classical
  set K₁ : Subgroup Y := kconj a K 1 with hK₁def
  have hK1 : ∀ x, x ∈ K₁ ↔ ∃ y ∈ K, x = a * y * a⁻¹ := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      exact ⟨y, hy, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, pow_one]⟩
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_map.2 ⟨y, hy, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, pow_one]⟩
  have hcenter1 : ∀ z ∈ K₁, (∀ y ∈ K₁, z * y = y * z) → z = 1 := by
    intro z hz hzc
    obtain ⟨k, hk, rfl⟩ := (hK1 z).1 hz
    have hk1 : k = 1 := by
      refine hcenter k hk fun y hy => ?_
      have h := hzc (a * y * a⁻¹) ((hK1 _).2 ⟨y, hy, rfl⟩)
      have h' : a * (k * y) * a⁻¹ = a * (y * k) * a⁻¹ := by
        calc a * (k * y) * a⁻¹ = a * k * a⁻¹ * (a * y * a⁻¹) := by group
          _ = a * y * a⁻¹ * (a * k * a⁻¹) := h
          _ = a * (y * k) * a⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h')
    rw [hk1]; simp
  have impl : ∀ f ∈ F, ∃ x ∈ K₁, ∀ y ∈ K₁, f * y * f⁻¹ = x * y * x⁻¹ := by
    intro f hf
    obtain ⟨k, hk, hfk⟩ := hFinner f hf
    refine ⟨a * k * a⁻¹, (hK1 _).2 ⟨k, hk, rfl⟩, fun y hy => ?_⟩
    have := act_kconj (hFa f hf) hfk 1 hy
    simpa only [pow_one] using this
  have uniq : ∀ x ∈ K₁, ∀ x' ∈ K₁, (∀ y ∈ K₁, x * y * x⁻¹ = x' * y * x'⁻¹) → x = x' := by
    intro x hx x' hx' h
    have hz : x'⁻¹ * x = 1 := by
      refine hcenter1 _ (K₁.mul_mem (K₁.inv_mem hx') hx) fun y hy => ?_
      have := h y hy
      calc x'⁻¹ * x * y = x'⁻¹ * (x * y * x⁻¹) * x := by group
        _ = x'⁻¹ * (x' * y * x'⁻¹) * x := by rw [this]
        _ = y * (x'⁻¹ * x) := by group
    exact (inv_mul_eq_one.1 hz).symm
  choose! κ hκmem hκ using impl
  have hκone : κ 1 = 1 := by
    refine uniq _ (hκmem 1 (Subgroup.one_mem _)) 1 (Subgroup.one_mem _) fun y hy => ?_
    rw [← hκ 1 (Subgroup.one_mem _) y hy]
  have hκmul : ∀ f ∈ F, ∀ g ∈ F, κ (f * g) = κ f * κ g := by
    intro f hf g hg
    refine uniq _ (hκmem _ (F.mul_mem hf hg)) _ (K₁.mul_mem (hκmem f hf) (hκmem g hg)) fun y hy => ?_
    rw [← hκ _ (F.mul_mem hf hg) y hy]
    have hgy : g * y * g⁻¹ ∈ K₁ := by
      rw [hκ g hg y hy]
      exact K₁.mul_mem (K₁.mul_mem (hκmem g hg) hy) (K₁.inv_mem (hκmem g hg))
    calc f * g * y * (f * g)⁻¹ = f * (g * y * g⁻¹) * f⁻¹ := by group
      _ = κ f * (g * y * g⁻¹) * (κ f)⁻¹ := hκ f hf _ hgy
      _ = κ f * (κ g * y * (κ g)⁻¹) * (κ f)⁻¹ := by rw [hκ g hg y hy]
      _ = κ f * κ g * y * (κ f * κ g)⁻¹ := by group
  let κhom : ↥F →* Y :=
    { toFun := fun f => κ f
      map_one' := hκone
      map_mul' := fun f g => hκmul f f.2 g g.2 }
  have hκhom : ∀ f : ↥F, κhom f = κ f := fun _ => rfl
  have hinj : Function.Injective κhom := by
    rw [injective_iff_map_eq_one]
    rintro ⟨f, hfF⟩ hf
    have hf1 : κ f = 1 := hf
    have hcK₁ : ∀ y ∈ K₁, f * y = y * f := by
      intro y hy
      have h := hκ f hfF y hy
      rw [hf1] at h
      simp only [one_mul, inv_one, mul_one] at h
      calc f * y = f * y * f⁻¹ * f := by group
        _ = y * f := by rw [h]
    have hcK : ∀ y ∈ K, f * y = y * f := by
      intro z hz
      have h := hcK₁ _ ((hK1 _).2 ⟨z, hz, rfl⟩)
      have hfa := hFa f hfF
      have hconj : a⁻¹ * f * a = f := by
        rw [mul_assoc, hfa, ← mul_assoc, inv_mul_cancel, one_mul]
      calc f * z = a⁻¹ * (a * f) * z := by group
        _ = a⁻¹ * (f * a) * z := by rw [hfa]
        _ = a⁻¹ * (f * (a * z * a⁻¹)) * a := by group
        _ = a⁻¹ * ((a * z * a⁻¹) * f) * a := by rw [h]
        _ = z * (a⁻¹ * f * a) := by group
        _ = z * f := by rw [hconj]
    exact Subtype.ext (hFfaith f hfF hcK)
  have hXK₁ : ∀ x ∈ κhom.range, x ∈ K₁ := by
    rintro _ ⟨f, rfl⟩
    exact hκmem f f.2
  have hXel : IsElemAbelian p κhom.range := by
    have hFtop : IsElemAbelian p (⊤ : Subgroup ↥F) := by
      have := hFel.subgroupOf F
      rwa [Subgroup.subgroupOf_self] at this
    rw [MonoidHom.range_eq_map]
    exact hFtop.map κhom
  refine ⟨κhom.range, hXel, ?_, fun x hx y hy => ?_, fun x hx f hf => ?_⟩
  · exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  · exact (hcomm01 y hy x (hXK₁ x hx)).symm
  · obtain ⟨g, rfl⟩ := hx
    have h1 := hκ f hf (κ g) (hκmem g g.2)
    have hcomm : κ f * κ g = κ g * κ f := by
      have := hXel.comm (a := κhom ⟨f, hf⟩) (b := κhom g) ⟨_, rfl⟩ ⟨_, rfl⟩
      exact this
    have h2 : f * κ g * f⁻¹ = κ g := by
      rw [h1]
      calc κ f * κ g * (κ f)⁻¹ = κ g * κ f * (κ f)⁻¹ := by rw [hcomm]
        _ = κ g := by group
    show (κ g) * f = f * κ g
    calc κ g * f = (f * κ g * f⁻¹) * f := by rw [h2]
      _ = f * κ g := by group

end Implementers


end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129W2

end
