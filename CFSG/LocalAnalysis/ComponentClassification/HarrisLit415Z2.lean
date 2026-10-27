module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Z
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415E8c

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ} {hs : Setting46e t L p f S w z V i j}
  {Kb₁ Kb₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} {W : Subgroup X} {z₁ : X}

namespace Config415

variable (hc : Config415 hs Kb₁ Kb₂ W z₁)
include hc

theorem Dstar_comm_z₁ {d : X}
    (hd : d ∈ S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
    d * z₁ = z₁ * d := by
  have hdW := hc.Dstar_le_W hd
  have hdM := hc.isSylowOf_W.le hdW
  have h1 : (QuotientGroup.mk ⟨d, hdM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      Standing.Setup42.KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) :=
    ⟨⟨d, hdM⟩, (mem_inf.mp hd).2, rfl⟩
  rw [hc.KBar_eq] at h1
  have h2 := hc.prod.le_normalizer₁ (mem_inf.mp h1).1
  exact (hc.comm_iff d hdW hdM).mpr ((L415.IsProd.mem_normalizer_iff_map _ _).mp h2)

theorem relIndex_V₀ {𝒱 : Subgroup X} (hW𝒱 : W ≤ 𝒱)
    (hstar : ∀ v ∈ 𝒱, v * z₁ * v⁻¹ = z₁ ∨ v * z₁ * v⁻¹ = t * z₁ * t⁻¹)
    (hz𝒱 : ∀ v ∈ 𝒱, z * v = v * z) : (𝒱 ⊓ centralizer {z₁}).relIndex 𝒱 = 2 := by
  have ht𝒱 := hW𝒱 hc.t_mem_W
  have hz₁2' : z₁ * z₁ = 1 := by rw [← sq]; exact hc.sq_z₁
  have hz₂ : t * z₁ * t⁻¹ = z₁ * z := by
    rw [hc.z_eq]
    calc t * z₁ * t⁻¹ = (z₁ * z₁) * (t * z₁ * t⁻¹) := by rw [hz₁2', one_mul]
      _ = z₁ * (z₁ * (t * z₁ * t⁻¹)) := by group
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨t, ht𝒱⟩, fun b => ?_⟩
  simp only [mem_subgroupOf, Subgroup.coe_mul, mem_inf, mem_centralizer_singleton_iff]
  by_cases hb : (b : X) * z₁ = z₁ * b
  · right
    refine ⟨⟨b.2, hb⟩, fun ⟨_, hbt⟩ => hc.t_not_comm ?_⟩
    calc t * z₁ = (b : X)⁻¹ * ((b * t) * z₁) := by group
      _ = (b : X)⁻¹ * (z₁ * (b * t)) := by rw [hbt]
      _ = (b : X)⁻¹ * (z₁ * b) * t := by group
      _ = (b : X)⁻¹ * (b * z₁) * t := by rw [hb]
      _ = z₁ * t := by group
  · left
    refine ⟨⟨mul_mem b.2 ht𝒱, ?_⟩, fun ⟨_, h1⟩ => hb h1⟩
    have h1 : (b : X) * z₁ * (b : X)⁻¹ = t * z₁ * t⁻¹ := by
      rcases hstar b b.2 with h2 | h2
      · exfalso
        apply hb
        calc (b : X) * z₁ = ((b : X) * z₁ * (b : X)⁻¹) * b := by group
          _ = z₁ * b := by rw [h2]
      · exact h2
    have h3 : (b : X) * z * (b : X)⁻¹ = z := by rw [← hz𝒱 b b.2]; group
    have h4 : (b : X) * (t * z₁ * t⁻¹) * (b : X)⁻¹ = z₁ := by
      rw [hz₂]
      calc (b : X) * (z₁ * z) * (b : X)⁻¹ = ((b : X) * z₁ * (b : X)⁻¹) * ((b : X) * z * (b : X)⁻¹)
            := by group
        _ = (z₁ * z) * z := by rw [h1, h3, hz₂]
        _ = z₁ := by
          have hz2 : z * z = 1 := by
            rw [← sq]; exact hs.setup.sq_eq_one_of_mem_X (subset_closure (by simp))
          rw [mul_assoc, hz2, mul_one]
    calc (b : X) * t * z₁ = ((b : X) * (t * z₁ * t⁻¹) * (b : X)⁻¹) * ((b : X) * t) := by group
      _ = z₁ * ((b : X) * t) := by rw [h4]

theorem center_V₀ (hKC : AutPSL2CentralizerInput) {𝒱 : Subgroup X} (h𝒱 : IsSylowOf 2 𝒱 ⊤)
    (hW𝒱 : W ≤ 𝒱) (hstar : ∀ v ∈ 𝒱, v * z₁ * v⁻¹ = z₁ ∨ v * z₁ * v⁻¹ = t * z₁ * t⁻¹)
    (hz𝒱 : ∀ v ∈ 𝒱, z * v = v * z) {τ : X} (hτ : τ ∈ 𝒱 ⊓ centralizer {z₁})
    (hτβ : τ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * τ⁻¹ =
      w ^ (orderOf w / 2) * t ^ i * z ^ j * z) :
    (center ↥(𝒱 ⊓ centralizer {z₁})).map (𝒱 ⊓ centralizer {z₁}).subtype =
      closure {z₁, t * z₁ * t⁻¹} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ := hs.setup
  have h45 := hs.lemma45
  set V₀ := 𝒱 ⊓ centralizer ({z₁} : Set X) with hV₀
  set A := (center ↥V₀).map V₀.subtype with hA
  have ht2 : t * t = 1 := by rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have ht𝒱 := hW𝒱 hc.t_mem_W
  have hz₁2' : z₁ * z₁ = 1 := by rw [← sq]; exact hc.sq_z₁
  have hz2 : z * z = 1 := by rw [← sq]; exact hσ.sq_eq_one_of_mem_X (subset_closure (by simp))
  have hz1 := hσ.z_ne_one
  have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
      1 := by
    rw [← sq]
    exact hσ.sq_eq_one_of_mem_X hs.beta.mem_X
  have hβW := hc.T_le_W (hσ.X_le_T hs.beta.mem_X)
  have hβV₀ : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ V₀ := mem_inf.mpr ⟨hW𝒱 hβW,
    mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp (hc.isSylowOf_W.le hc.z₁_mem)).symm⟩
  have hmemA : ∀ a, a ∈ A ↔ a ∈ V₀ ∧ ∀ y ∈ V₀, a * y = y * a := by
    intro a
    constructor
    · rintro ⟨a', ha', rfl⟩
      exact ⟨a'.2, fun y hy => congrArg Subtype.val ((mem_center_iff.mp ha') ⟨y, hy⟩).symm⟩
    · rintro ⟨haV, hac⟩
      exact ⟨⟨a, haV⟩, mem_center_iff.mpr fun g => Subtype.ext (hac g g.2).symm, rfl⟩
  have hidx := hc.relIndex_V₀ hW𝒱 hstar hz𝒱
  have hn : (V₀.subgroupOf 𝒱).Normal := Subgroup.normal_of_index_eq_two hidx
  have hV₀n : ∀ v ∈ 𝒱, ∀ y ∈ V₀, v * y * v⁻¹ ∈ V₀ := fun v hv y hy =>
    hn.conj_mem ⟨y, (mem_inf.mp hy).1⟩ hy ⟨v, hv⟩
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    ((hmemA a).mp ha).2 b ((hmemA b).mp hb).1
  have hAp : IsPGroup 2 A := h𝒱.isPGroup.to_le (fun a ha => ((mem_inf.mp ((hmemA a).mp ha).1).1))
  have htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A := by
    intro a ha
    obtain ⟨haV, hac⟩ := (hmemA a).mp ha
    refine (hmemA _).mpr ⟨hV₀n t ht𝒱 a haV, fun y hy => ?_⟩
    have hy' : t⁻¹ * y * t ∈ V₀ := by
      have := hV₀n t⁻¹ (inv_mem ht𝒱) y hy
      rwa [inv_inv] at this
    have h1 := hac _ hy'
    calc t * a * t⁻¹ * y = t * (a * (t⁻¹ * y * t)) * t⁻¹ := by group
      _ = t * ((t⁻¹ * y * t) * a) * t⁻¹ := by rw [h1]
      _ = y * (t * a * t⁻¹) := by group
  obtain ⟨x, hxD, hx2, -, hxC⟩ := hc.exists_x
  have hxDs : x ∉ S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
    intro hx
    obtain ⟨m, hm, ⟨eDs⟩⟩ := h45.dihedral_Dstar
    have hxz : x = 1 ∨ x = z := hxC x hx rfl
    have hall : ∀ d ∈ S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j),
        d = 1 ∨ d = z := by
      intro d hd
      apply hxC d hd
      rcases hxz with h1 | h1
      · rw [h1, one_mul, mul_one]
      · rw [h1]
        have hz' : z ∈ (S ⊓ L) ⊓ centralizer ((S ⊓ L : Subgroup X) : Set X) := by
          rw [hσ.center_D]
          exact mem_zpowers z
        exact ((Subgroup.mem_centralizer_iff.mp (mem_inf.mp hz').2) d (mem_inf.mp hd).1)
    have h1 : S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) ≤
        zpowers z := fun d hd => by
      rcases hall d hd with h2 | h2 <;> rw [h2]
      · exact one_mem _
      · exact mem_zpowers z
    have h2 := Subgroup.card_le_of_le h1
    rw [Nat.card_congr eDs.toEquiv, DihedralGroup.nat_card, L415.card_zpowers_two hz2 hz1] at h2
    have h3 : 4 ≤ 2 ^ m :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have hxW : x ∈ W := hc.T_le_W (mem_sup_left (mem_sup_right hxD))
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp (hs.sylow.le (mem_inf.mp hxD).1)
  obtain ⟨α, hαW, hαz, hα⟩ : ∃ α ∈ W, α * z₁ = z₁ * α ∧ (α = x ∨ α = x * t) := by
    by_cases hxz : x * z₁ = z₁ * x
    · exact ⟨x, hxW, hxz, Or.inl rfl⟩
    · exact ⟨x * t, mul_mem hxW hc.t_mem_W, hc.mul_t x hxW hxz, Or.inr rfl⟩
  have hαV₀ : α ∈ V₀ := mem_inf.mpr ⟨hW𝒱 hαW, mem_centralizer_singleton_iff.mpr hαz⟩
  have hidxD : ((S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)).subgroupOf
      (S ⊓ L)).index = 2 := h45.relIndex_Dstar
  have hC : ∀ a ∈ A, a * t = t * a → a = 1 ∨ a = z := by
    intro a ha hat
    obtain ⟨haV, hac⟩ := (hmemA a).mp ha
    have haW : a ∈ W := by
      rw [← hc.inf_V_beta h𝒱 hW𝒱]
      exact mem_inf.mpr ⟨(mem_inf.mp haV).1, mem_centralizer_singleton_iff.mpr (hac _ hβV₀)⟩
    have haT : a ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
      rw [← hσ.inf_W_t hKC hs.beta hc.isSylowOf_W hc.U_le]
      exact mem_inf.mpr ⟨haW, mem_centralizer_singleton_iff.mpr hat⟩
    have hax : a * x = x * a := by
      have h1 := hac α hαV₀
      rcases hα with rfl | rfl
      · exact h1
      · calc a * x = a * (x * t) * t⁻¹ := by group
          _ = x * t * a * t⁻¹ := by rw [h1]
          _ = x * (t * a) * t⁻¹ := by group
          _ = x * (a * t) * t⁻¹ := by rw [hat]
          _ = x * a := by group
    have haD : ∀ d ∈ S ⊓ L, a * d = d * a := by
      intro d hd
      by_cases hdDs : d ∈ S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)
      · exact hac d (mem_inf.mpr ⟨hW𝒱 (hc.Dstar_le_W hdDs),
          mem_centralizer_singleton_iff.mpr (hc.Dstar_comm_z₁ hdDs)⟩)
      · have h1 := (Subgroup.mul_mem_iff_of_index_two hidxD (a := (⟨x, hxD⟩ : ↥(S ⊓ L))⁻¹)
          (b := ⟨d, hd⟩)).mpr (iff_of_false (fun h => hxDs (by
            have := inv_mem h
            rw [inv_inv] at this
            exact this)) hdDs)
        have h2 : x⁻¹ * d ∈ S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) :=
          h1
        have h3 := hac _ (mem_inf.mpr ⟨hW𝒱 (hc.Dstar_le_W h2),
          mem_centralizer_singleton_iff.mpr (hc.Dstar_comm_z₁ h2)⟩)
        calc a * d = a * x * (x⁻¹ * d) := by group
          _ = x * a * (x⁻¹ * d) := by rw [hax]
          _ = x * (a * (x⁻¹ * d)) := by group
          _ = x * ((x⁻¹ * d) * a) := by rw [h3]
          _ = d * a := by group
    have haX : a ∈ closure {t, w ^ (orderOf w / 2), z} := by
      rw [← hσ.centralizer_D]
      exact mem_inf.mpr ⟨hσ.T_le haT, Subgroup.mem_centralizer_iff.mpr fun d hd =>
        (haD d hd).symm⟩
    have haβz : a ∈ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ⊔ zpowers z := by
      rw [← hc.inf_X_centralizer]
      exact mem_inf.mpr ⟨haX, (mem_inf.mp haV).2⟩
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := L415.mem_sup_of_commute hc.comm_beta_z haβz
    have hτc := hac τ hτ
    have hτz : τ * z * τ⁻¹ = z := by rw [← hz𝒱 τ (mem_inf.mp hτ).1]; group
    rcases L415.mem_zpowers_two hβ2 ha₁ with h1 | h1 <;>
      rcases L415.mem_zpowers_two hz2 ha₂ with h2 | h2 <;> rw [h1, h2]
    · left
      group
    · right
      group
    · exfalso
      apply hz1
      have h3 : τ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * τ⁻¹ =
          w ^ (orderOf w / 2) * t ^ i * z ^ j := by
        rw [h1, h2, mul_one] at hτc
        rw [← hτc]
        group
      rw [hτβ] at h3
      calc z = (w ^ (orderOf w / 2) * t ^ i * z ^ j)⁻¹ *
          (w ^ (orderOf w / 2) * t ^ i * z ^ j * z) := by group
        _ = 1 := by rw [h3, inv_mul_cancel]
    · exfalso
      apply hz1
      have h3 : τ * (w ^ (orderOf w / 2) * t ^ i * z ^ j * z) * τ⁻¹ =
          w ^ (orderOf w / 2) * t ^ i * z ^ j * z := by
        rw [h1, h2] at hτc
        rw [← hτc]
        group
      rw [show τ * (w ^ (orderOf w / 2) * t ^ i * z ^ j * z) * τ⁻¹ =
        (τ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * τ⁻¹) * (τ * z * τ⁻¹) by group, hτβ,
        hτz] at h3
      calc z = (w ^ (orderOf w / 2) * t ^ i * z ^ j * z)⁻¹ *
          (w ^ (orderOf w / 2) * t ^ i * z ^ j * z * z) := by group
        _ = 1 := by rw [h3, inv_mul_cancel]
  have hz₁A : z₁ ∈ A := (hmemA z₁).mpr ⟨mem_inf.mpr ⟨hW𝒱 hc.z₁_mem,
    mem_centralizer_singleton_iff.mpr rfl⟩, fun y hy =>
      (mem_centralizer_singleton_iff.mp (mem_inf.mp hy).2).symm⟩
  have hzA : z ∈ A := (hmemA z).mpr ⟨mem_inf.mpr ⟨hW𝒱 (hc.T_le_W (hσ.X_le_T
    (subset_closure (by simp)))), mem_centralizer_singleton_iff.mpr (hc.comm_z hc.z₁_mem).symm⟩,
      fun y hy => hz𝒱 y (mem_inf.mp hy).1⟩
  have hz₂ : t * z₁ * t⁻¹ = z₁ * z := by
    rw [hc.z_eq]
    calc t * z₁ * t⁻¹ = (z₁ * z₁) * (t * z₁ * t⁻¹) := by rw [hz₁2', one_mul]
      _ = z₁ * (z₁ * (t * z₁ * t⁻¹)) := by group
  have hZA : zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹) ≤ A :=
    sup_le (zpowers_le.mpr hz₁A) (zpowers_le.mpr (hz₂ ▸ mul_mem hz₁A hzA))
  have hZ4 : Nat.card ↥(zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹)) = 4 := by
    have h1 := hc.card_Y₃
    have hz₁1 : z₁ ≠ 1 := fun h => hc.z₁_ne (by rw [h]; group)
    obtain ⟨hB₁c, hB₁2⟩ := L415.elem_zpowers hz₁2'
    have hz₂2 : (t * z₁ * t⁻¹) * (t * z₁ * t⁻¹) = 1 := by
      rw [show t * z₁ * t⁻¹ * (t * z₁ * t⁻¹) = t * (z₁ * z₁) * t⁻¹ by group, hz₁2']
      group
    have hz₂B₁ : t * z₁ * t⁻¹ ∉ zpowers z₁ := fun h2 => by
      rcases L415.mem_zpowers_two hz₁2' h2 with h3 | h3
      · apply hz₁1
        calc z₁ = t⁻¹ * (t * z₁ * t⁻¹) * t := by group
          _ = 1 := by rw [h3]; group
      · exact hc.z₁_ne h3.symm
    obtain ⟨-, -, hcard⟩ := L415.elem_sup hB₁c hB₁2 hz₂2 hz₂B₁ (fun a ha => by
      rcases L415.mem_zpowers_two hz₁2' ha with rfl | rfl
      · simp
      · exact hc.z₁_comm_z₂)
    rw [hcard, L415.card_zpowers_two hz₁2' hz₁1]
  have h1 := L415.eq_of_centralizer_le hAc hAp ht2 htA hC hz₁2' hc.z_eq hz1 hZA hZ4
  rw [h1, show ({z₁, t * z₁ * t⁻¹} : Set X) = {z₁} ∪ {t * z₁ * t⁻¹} from rfl,
    Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure]

end Config415

end CFSG.ComponentClassification.HarrisLit
