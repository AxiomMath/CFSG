module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Z2

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ} {hs : Setting46e t L p f S w z V i j}
  {Kb₁ Kb₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} {W : Subgroup X} {z₁ : X}

namespace Config415

variable (hc : Config415 hs Kb₁ Kb₂ W z₁)
include hc

theorem exists_alpha [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) {𝒱 : Subgroup X}
    (h𝒱 : IsSylowOf 2 𝒱 ⊤) (hW𝒱 : W ≤ 𝒱)
    (hstar : ∀ v ∈ 𝒱, v * z₁ * v⁻¹ = z₁ ∨ v * z₁ * v⁻¹ = t * z₁ * t⁻¹)
    (hz𝒱 : ∀ v ∈ 𝒱, z * v = v * z) :
    ∃ α g : X, α ∈ 𝒱 ⊓ centralizer {z₁} ∧ g * t * g⁻¹ = α ∧
      S.map (MulAut.conj g).toMonoidHom = 𝒱 ⊓ centralizer {α} ∧
      (closure {t, w ^ (orderOf w / 2), z}).map (MulAut.conj g).toMonoidHom =
        closure {α, z₁, t * z₁ * t⁻¹} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ := hs.setup
  set V₀ := 𝒱 ⊓ centralizer ({z₁} : Set X) with hV₀
  have ht2 : t * t = 1 := by rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]
  have ht𝒱 := hW𝒱 hc.t_mem_W
  have htV₀ : t ∉ V₀ := fun h1 => hc.t_not_comm (mem_centralizer_singleton_iff.mp (mem_inf.mp h1).2)
  have hidx := hc.relIndex_V₀ hW𝒱 hstar hz𝒱
  have hPidx : ¬ 2 ∣ 𝒱.index := by
    have := (isSylowOf_iff.mp h𝒱).2.2
    rwa [Subgroup.relIndex_top_right] at this
  obtain ⟨g₀, hg₀V₀, hext, hgc⟩ := HarrisEnd.exists_extremal_conj_of_relIndex_two hnab
    h𝒱.isPGroup hPidx inf_le_left hidx ht𝒱 htV₀ (by rw [sq]; exact ht2)
  set α := g₀⁻¹ * t * g₀ with hα
  have hαSyl : IsSylowOf 2 (𝒱 ⊓ centralizer {α}) (centralizer {α}) := isSylowOf_iff.mpr hext
  have hSα : IsSylowOf 2 (S.map (MulAut.conj g₀⁻¹).toMonoidHom) (centralizer {α}) := by
    have h1 := HarrisLit.isSylowOf_map (MulAut.conj g₀⁻¹).toMonoidHom hs.sylow
    rwa [L415.map_conj_centralizer, show g₀⁻¹ * t * g₀⁻¹⁻¹ = α by rw [hα, inv_inv]] at h1
  obtain ⟨k, hk, hkS⟩ := L415.exists_map_conj hSα hαSyl
  set g := k * g₀⁻¹ with hg
  have hkα : k * α = α * k := mem_centralizer_singleton_iff.mp hk
  have hgt : g * t * g⁻¹ = α := by
    calc g * t * g⁻¹ = k * α * k⁻¹ := by rw [hg, hα]; group
      _ = α := by rw [hkα]; group
  have hgS : S.map (MulAut.conj g).toMonoidHom = 𝒱 ⊓ centralizer {α} := by
    rw [hkS, Subgroup.map_map, hg]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  refine ⟨α, g, hg₀V₀, hgt, hgS, ?_⟩
  have hn : (V₀.subgroupOf 𝒱).Normal := Subgroup.normal_of_index_eq_two hidx
  have hV₀n : ∀ v ∈ 𝒱, ∀ y ∈ V₀, v * y * v⁻¹ ∈ V₀ := fun v hv y hy =>
    hn.conj_mem ⟨y, (mem_inf.mp hy).1⟩ hy ⟨v, hv⟩
  set S₀ := (V₀ ⊓ centralizer {α}).map (MulAut.conj g⁻¹).toMonoidHom with hS₀
  have hmemS : ∀ x, x ∈ S ↔ g * x * g⁻¹ ∈ 𝒱 ⊓ centralizer {α} := by
    intro x
    rw [← hgS]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have h1 : y = x := by
        have := congrArg (fun u => g⁻¹ * u * g) hyx
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
        rw [show g⁻¹ * (g * y * g⁻¹) * g = y by group,
          show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
        exact this
      rwa [← h1]
  have hmemS₀ : ∀ x, x ∈ S₀ ↔ g * x * g⁻¹ ∈ V₀ ⊓ centralizer {α} := by
    intro x
    rw [hS₀, Subgroup.mem_map_equiv]
    simp [MulAut.conj_apply]
  have hS₀S : S₀ ≤ S := fun x hx => by
    rw [hmemS]
    have h1 := (hmemS₀ x).mp hx
    exact mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp h1).1).1, (mem_inf.mp h1).2⟩
  have hS₀n : ∀ c ∈ S, ∀ y ∈ S₀, c * y * c⁻¹ ∈ S₀ := by
    intro c hc' y hy
    rw [hmemS₀]
    have hc'' := (hmemS c).mp hc'
    have hy' := (hmemS₀ y).mp hy
    have h1 : g * (c * y * c⁻¹) * g⁻¹ = (g * c * g⁻¹) * (g * y * g⁻¹) * (g * c * g⁻¹)⁻¹ := by
      group
    rw [h1]
    refine mem_inf.mpr ⟨hV₀n _ (mem_inf.mp hc'').1 _ (mem_inf.mp hy').1, ?_⟩
    exact mul_mem (mul_mem (mem_inf.mp hc'').2 (mem_inf.mp hy').2) (inv_mem (mem_inf.mp hc'').2)
  have hS₀n' : ∀ c ∈ S, ∀ y ∈ S₀, c⁻¹ * y * c ∈ S₀ := fun c hc' y hy => by
    have := hS₀n c⁻¹ (inv_mem hc') y hy
    rwa [inv_inv] at this
  set F := L415.centralInv S₀ with hF
  have hFX : F ≤ closure {t, w ^ (orderOf w / 2), z} := by
    refine hσ.le_X_of_normal_S (fun x hx => hS₀S ((L415.mem_centralInv.mp hx).1)) ?_ ?_
    · intro d hd x hx
      exact L415.conj_mem_centralInv (hS₀n d hd.1) (hS₀n' d hd.1) hx
    · intro x hx
      rw [sq]
      exact (L415.mem_centralInv.mp hx).2.2
  have hz₁2' : z₁ * z₁ = 1 := by rw [← sq]; exact hc.sq_z₁
  have hz2 : z * z = 1 := by rw [← sq]; exact hσ.sq_eq_one_of_mem_X (subset_closure (by simp))
  have hz₂ : t * z₁ * t⁻¹ = z₁ * z := by
    rw [hc.z_eq]
    calc t * z₁ * t⁻¹ = (z₁ * z₁) * (t * z₁ * t⁻¹) := by rw [hz₁2', one_mul]
      _ = z₁ * (z₁ * (t * z₁ * t⁻¹)) := by group
  have hαz₁ : α * z₁ = z₁ * α := mem_centralizer_singleton_iff.mp (mem_inf.mp hg₀V₀).2
  have hαz : α * z = z * α := (hz𝒱 α (mem_inf.mp hg₀V₀).1).symm
  have hα2 : α * α = 1 := by
    rw [hα, show g₀⁻¹ * t * g₀ * (g₀⁻¹ * t * g₀) = g₀⁻¹ * (t * t) * g₀ by group, ht2]
    group
  have hmemF : ∀ y ∈ V₀ ⊓ centralizer {α}, (∀ c ∈ V₀ ⊓ centralizer {α}, y * c = c * y) →
      y * y = 1 → g⁻¹ * y * g ∈ F := by
    intro y hy hyc hy2
    refine L415.mem_centralInv.mpr ⟨(hmemS₀ _).mpr ?_, fun c hc' => ?_, ?_⟩
    · rw [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
      exact hy
    · have h2 := hyc _ ((hmemS₀ c).mp hc')
      calc g⁻¹ * y * g * c = g⁻¹ * (y * (g * c * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * c * g⁻¹) * y) * g := by rw [h2]
        _ = c * (g⁻¹ * y * g) := by group
    · rw [show g⁻¹ * y * g * (g⁻¹ * y * g) = g⁻¹ * (y * y) * g by group, hy2]
      group
  have hz₁V₀ : z₁ ∈ V₀ := mem_inf.mpr ⟨hW𝒱 hc.z₁_mem, mem_centralizer_singleton_iff.mpr rfl⟩
  have hzV₀ : z ∈ V₀ := mem_inf.mpr ⟨hW𝒱 (hc.T_le_W (hσ.X_le_T (subset_closure (by simp)))),
    mem_centralizer_singleton_iff.mpr (hc.comm_z hc.z₁_mem).symm⟩
  have hαF : g⁻¹ * α * g ∈ F := by
    refine hmemF α (mem_inf.mpr ⟨(mem_inf.mp hg₀V₀), mem_centralizer_singleton_iff.mpr rfl⟩)
      (fun c hc' => (mem_centralizer_singleton_iff.mp (mem_inf.mp hc').2).symm) hα2
  have hz₁F : g⁻¹ * z₁ * g ∈ F := by
    refine hmemF z₁ (mem_inf.mpr ⟨hz₁V₀, mem_centralizer_singleton_iff.mpr hαz₁.symm⟩)
      (fun c hc' => (mem_centralizer_singleton_iff.mp (mem_inf.mp (mem_inf.mp hc').1).2).symm)
      hz₁2'
  have hz₂F : g⁻¹ * (t * z₁ * t⁻¹) * g ∈ F := by
    rw [hz₂]
    have hzc : ∀ c ∈ V₀, z * c = c * z := fun c hc' => hz𝒱 c (mem_inf.mp hc').1
    have hz₁z2 : z₁ * z * (z₁ * z) = 1 := by
      calc z₁ * z * (z₁ * z) = z₁ * (z * z₁) * z := by group
        _ = z₁ * (z₁ * z) * z := by rw [hzc z₁ hz₁V₀]
        _ = (z₁ * z₁) * (z * z) := by group
        _ = 1 := by rw [hz₁2', hz2, one_mul]
    refine hmemF (z₁ * z) (mem_inf.mpr ⟨mul_mem hz₁V₀ hzV₀, mem_centralizer_singleton_iff.mpr ?_⟩)
      (fun c hc' => ?_) hz₁z2
    · calc z₁ * z * α = z₁ * (z * α) := by group
        _ = z₁ * (α * z) := by rw [hαz]
        _ = (z₁ * α) * z := by group
        _ = (α * z₁) * z := by rw [hαz₁]
        _ = α * (z₁ * z) := by group
    · have h1 := (mem_centralizer_singleton_iff.mp (mem_inf.mp (mem_inf.mp hc').1).2).symm
      have h2 := hzc c (mem_inf.mp hc').1
      calc z₁ * z * c = z₁ * (z * c) := by group
        _ = z₁ * (c * z) := by rw [h2]
        _ = (z₁ * c) * z := by group
        _ = (c * z₁) * z := by rw [h1]
        _ = c * (z₁ * z) := by group
  have hmemXg : ∀ y, g⁻¹ * y * g ∈ closure {t, w ^ (orderOf w / 2), z} →
      y ∈ (closure {t, w ^ (orderOf w / 2), z}).map (MulAut.conj g).toMonoidHom := fun y hy =>
    ⟨g⁻¹ * y * g, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hle : closure {α, z₁, t * z₁ * t⁻¹} ≤
      (closure {t, w ^ (orderOf w / 2), z}).map (MulAut.conj g).toMonoidHom := by
    rw [closure_le]
    rintro y (rfl | rfl | rfl)
    · exact hmemXg _ (hFX hαF)
    · exact hmemXg _ (hFX hz₁F)
    · exact hmemXg _ (hFX hz₂F)
  have hz₁1 : z₁ ≠ 1 := fun h1 => hc.z₁_ne (by rw [h1]; group)
  have hz₂2 : (t * z₁ * t⁻¹) * (t * z₁ * t⁻¹) = 1 := by
    rw [show t * z₁ * t⁻¹ * (t * z₁ * t⁻¹) = t * (z₁ * z₁) * t⁻¹ by group, hz₁2']
    group
  obtain ⟨hB₁c, hB₁2⟩ := L415.elem_zpowers hz₁2'
  have hz₂B₁ : t * z₁ * t⁻¹ ∉ zpowers z₁ := fun h1 => by
    rcases L415.mem_zpowers_two hz₁2' h1 with h2 | h2
    · apply hz₁1
      calc z₁ = t⁻¹ * (t * z₁ * t⁻¹) * t := by group
        _ = 1 := by rw [h2]; group
    · exact hc.z₁_ne h2.symm
  obtain ⟨hB₂c, hB₂2, hB₂⟩ := L415.elem_sup hB₁c hB₁2 hz₂2 hz₂B₁ (fun a ha => by
    rcases L415.mem_zpowers_two hz₁2' ha with rfl | rfl
    · simp
    · exact hc.z₁_comm_z₂)
  have hαB₂ : α ∉ zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹) := by
    intro h1
    apply hc.not_le_centralizer_conj g₀⁻¹
    rw [inv_inv, ← hα]
    intro x hx
    have hxz₁ : z₁ ∈ centralizer ({x} : Set X) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2).symm
    have hxz₂ : t * z₁ * t⁻¹ ∈ centralizer ({x} : Set X) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hc.W₀_le_z₂ hx)).symm
    have h2 := (sup_le (zpowers_le.mpr hxz₁) (zpowers_le.mpr hxz₂)) h1
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp h2).symm
  have hαc : ∀ a ∈ zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹), a * α = α * a := by
    have hαz₂ : t * z₁ * t⁻¹ * α = α * (t * z₁ * t⁻¹) := by
      rw [hz₂]
      calc z₁ * z * α = z₁ * (z * α) := by group
        _ = z₁ * (α * z) := by rw [hαz]
        _ = (z₁ * α) * z := by group
        _ = (α * z₁) * z := by rw [hαz₁]
        _ = α * (z₁ * z) := by group
    have hle' : zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹) ≤ centralizer {α} :=
      sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hαz₁.symm))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hαz₂))
    exact fun a ha => mem_centralizer_singleton_iff.mp (hle' ha)
  obtain ⟨-, -, hB₃⟩ := L415.elem_sup hB₂c hB₂2 hα2 hαB₂ hαc
  have hcl : closure {α, z₁, t * z₁ * t⁻¹} =
      (zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹)) ⊔ zpowers α := by
    rw [show ({α, z₁, t * z₁ * t⁻¹} : Set X) = {α} ∪ ({z₁} ∪ {t * z₁ * t⁻¹}) by
      rw [Set.insert_eq, Set.insert_eq], Subgroup.closure_union, Subgroup.closure_union,
      ← zpowers_eq_closure, ← zpowers_eq_closure, ← zpowers_eq_closure, sup_comm]
  have hcard₁ : Nat.card ↥(closure {α, z₁, t * z₁ * t⁻¹}) = 8 := by
    rw [hcl, hB₃, hB₂, L415.card_zpowers_two hz₁2' hz₁1]
  have hcard₂ : Nat.card ↥((closure {t, w ^ (orderOf w / 2), z}).map
      (MulAut.conj g).toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hσ.card_X]
  exact (eq_of_le_of_card_ge hle (by rw [hcard₁, hcard₂])).symm

end Config415

end CFSG.ComponentClassification.HarrisLit
