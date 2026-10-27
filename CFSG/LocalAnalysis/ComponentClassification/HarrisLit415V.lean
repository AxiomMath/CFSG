module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415KX
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415K2

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ} {hs : Setting46e t L p f S w z V i j}
  {Kb₁ Kb₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} {W : Subgroup X} {z₁ : X}

theorem Setting46e.beta_not_mem_zpowers_z (hs : Setting46e t L p f S w z V i j) :
    w ^ (orderOf w / 2) * t ^ i * z ^ j ∉ zpowers z := by
  intro h1
  apply hs.beta.not_mem
  exact (zpowers_le.mpr (mem_sup_right hs.setup.z_mem)) h1

namespace Config415

variable (hc : Config415 hs Kb₁ Kb₂ W z₁)
include hc

theorem card_beta_z :
    Nat.card ↥(zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ⊔ zpowers z) = 4 := by
  have hσ := hs.setup
  have hz2 : z * z = 1 := by rw [← sq]; exact hσ.sq_eq_one_of_mem_X (subset_closure (by simp))
  have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
      1 := by
    rw [← sq]
    exact hσ.sq_eq_one_of_mem_X hs.beta.mem_X
  obtain ⟨hzc, hz2'⟩ := L415.elem_zpowers hz2
  obtain ⟨-, -, hcard⟩ := L415.elem_sup hzc hz2' hβ2 hs.beta_not_mem_zpowers_z (fun a ha => by
    rcases L415.mem_zpowers_two hz2 ha with rfl | rfl
    · simp
    · exact hσ.X_comm (subset_closure (by simp)) hs.beta.mem_X)
  rw [sup_comm, hcard, L415.card_zpowers_two hz2 hσ.z_ne_one]

theorem inf_X_centralizer :
    closure {t, w ^ (orderOf w / 2), z} ⊓ centralizer {z₁} =
      zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ⊔ zpowers z := by
  have hσ := hs.setup
  have hzX : z ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have htX : t ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have hβz₁ : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ centralizer ({z₁} : Set X) :=
    mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp (hc.isSylowOf_W.le hc.z₁_mem)).symm
  have hzz₁ : z ∈ centralizer ({z₁} : Set X) :=
    mem_centralizer_singleton_iff.mpr (hc.comm_z hc.z₁_mem).symm
  have hle : zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ⊔ zpowers z ≤
      closure {t, w ^ (orderOf w / 2), z} ⊓ centralizer {z₁} :=
    sup_le (zpowers_le.mpr (mem_inf.mpr ⟨hs.beta.mem_X, hβz₁⟩))
      (zpowers_le.mpr (mem_inf.mpr ⟨hzX, hzz₁⟩))
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [hc.card_beta_z]
  have h8 := hσ.card_X
  have hdvd : Nat.card ↥(closure {t, w ^ (orderOf w / 2), z} ⊓ centralizer {z₁}) ∣ 8 := by
    rw [← h8]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hne : Nat.card ↥(closure {t, w ^ (orderOf w / 2), z} ⊓ centralizer {z₁}) ≠ 8 := by
    intro h1
    have h2 : closure {t, w ^ (orderOf w / 2), z} ⊓ centralizer {z₁} =
        closure {t, w ^ (orderOf w / 2), z} :=
      eq_of_le_of_card_ge inf_le_left (by rw [h1, h8])
    have h3 : t ∈ closure {t, w ^ (orderOf w / 2), z} ⊓ centralizer {z₁} := by
      rw [h2]
      exact htX
    exact hc.t_not_comm (mem_centralizer_singleton_iff.mp (mem_inf.mp h3).2)
  have h4 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases h : Nat.card ↥(closure {t, w ^ (orderOf w / 2), z} ⊓ centralizer {z₁}) <;>
    simp_all

theorem mem_center_W (hKC : AutPSL2CentralizerInput) {c : X} (hcW : c ∈ W)
    (hcc : ∀ y ∈ W, c * y = y * c) :
    c = 1 ∨ c = w ^ (orderOf w / 2) * t ^ i * z ^ j ∨ c = z ∨
      c = w ^ (orderOf w / 2) * t ^ i * z ^ j * z := by
  have hσ := hs.setup
  have hCWt := hσ.inf_W_t hKC hs.beta hc.isSylowOf_W hc.U_le
  have hcT : c ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
    rw [← hCWt]
    exact mem_inf.mpr ⟨hcW, mem_centralizer_singleton_iff.mpr (hcc t hc.t_mem_W)⟩
  have hcX : c ∈ closure {t, w ^ (orderOf w / 2), z} := by
    rw [← hσ.centralizer_D]
    refine mem_inf.mpr ⟨hσ.T_le hcT, Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
    exact (hcc d (hc.T_le_W (mem_sup_left (mem_sup_right hd)))).symm
  have hcz : c ∈ closure {t, w ^ (orderOf w / 2), z} ⊓ centralizer {z₁} :=
    mem_inf.mpr ⟨hcX, mem_centralizer_singleton_iff.mpr (hcc z₁ hc.z₁_mem)⟩
  rw [hc.inf_X_centralizer] at hcz
  have hz2 : z * z = 1 := by rw [← sq]; exact hσ.sq_eq_one_of_mem_X (subset_closure (by simp))
  have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
      1 := by
    rw [← sq]
    exact hσ.sq_eq_one_of_mem_X hs.beta.mem_X
  have hcomm : ∀ a ∈ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j), ∀ b ∈ zpowers z,
      a * b = b * a := by
    intro a ha b hb
    rcases L415.mem_zpowers_two hβ2 ha with rfl | rfl <;>
      rcases L415.mem_zpowers_two hz2 hb with rfl | rfl <;> try simp
    exact hσ.X_comm hs.beta.mem_X (subset_closure (by simp))
  obtain ⟨a, ha, b, hb, rfl⟩ := L415.mem_sup_of_commute hcomm hcz
  rcases L415.mem_zpowers_two hβ2 ha with rfl | rfl <;>
    rcases L415.mem_zpowers_two hz2 hb with rfl | rfl <;> simp

theorem card_V_le {𝒱 : Subgroup X} (h𝒱 : IsSylowOf 2 𝒱 ⊤) : Nat.card 𝒱 ≤ 4 * Nat.card W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := hs.beta.twoPart_le
  rw [twoPart, twoPart, ← h𝒱.card_eq, ← hc.isSylowOf_W.card_eq] at h1
  exact h1

theorem inf_V_beta {𝒱 : Subgroup X} (h𝒱 : IsSylowOf 2 𝒱 ⊤) (hW𝒱 : W ≤ 𝒱) :
    𝒱 ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} = W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hc.isSylowOf_W.eq_of_le (le_inf hW𝒱 hc.isSylowOf_W.le) inf_le_right
    (h𝒱.isPGroup.to_le inf_le_left)

theorem exists_V [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKC : AutPSL2CentralizerInput) (hA : AutPSL2RCentralizerInput)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j)) :
    ∃ (𝒱 : Subgroup X) (τ : X), IsSylowOf 2 𝒱 ⊤ ∧ W ≤ 𝒱 ∧ τ ∈ 𝒱 ∧
      τ ∈ normalizer (W : Set X) ∧ τ * z₁ = z₁ * τ ∧ τ * z * τ⁻¹ = z ∧
      τ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * τ⁻¹ =
        w ^ (orderOf w / 2) * t ^ i * z ^ j * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ := hs.setup
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβdef
  have hW := hc.isSylowOf_W
  obtain ⟨Q, hQ, hWQ⟩ := exists_isSylowOf_ge hW.isPGroup (le_top : W ≤ ⊤)
  have hWQ' : W ≠ Q := fun h1 => hc.not_isSylowOf hnab hKC (h1 ▸ hQ)
  have hlt : W.subgroupOf Q < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hWQ' (le_antisymm hWQ fun x hx => ?_)
    have : (⟨x, hx⟩ : Q) ∈ W.subgroupOf Q := h ▸ mem_top _
    exact this
  have hnil : Group.IsNilpotent Q := hQ.isPGroup.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := Q) _ hlt
  obtain ⟨y, hyN, hyW⟩ := IsConcreteLE.exists_of_lt hnc
  have hyN' : (y : X) ∈ normalizer (W : Set X) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxQ : x ∈ Q := hWQ hx
      exact (mem_normalizer_iff.mp hyN ⟨x, hxQ⟩).mp (show (⟨x, hxQ⟩ : Q) ∈ W.subgroupOf Q
        from hx)
    · intro hx
      have hxQ : x ∈ Q := by
        have h1 : (y : X)⁻¹ * (y * x * (y : X)⁻¹) * y ∈ Q :=
          mul_mem (mul_mem (inv_mem y.2) (hWQ hx)) y.2
        rwa [show (y : X)⁻¹ * (y * x * (y : X)⁻¹) * y = x by group] at h1
      exact (mem_normalizer_iff.mp hyN ⟨x, hxQ⟩).mpr hx
  have hyW' : (y : X) ∉ W := hyW
  have hyβ : (y : X) ∉ centralizer {β} := by
    intro h1
    apply hyW'
    rw [← hc.inf_V_beta hQ hWQ]
    exact mem_inf.mpr ⟨y.2, h1⟩
  have hz₂ := hc.conj_mem_of_normalizer_W hnab hKC hA h412 hyN'
  have hz₂' := hc.conj_mem_of_normalizer_W hnab hKC hA h412
    (mul_mem hyN' (le_normalizer hc.t_mem_W))
  have hz₁₂ := hc.z₁_comm_z₂
  have hyz : (y : X) * z * (y : X)⁻¹ = z := by
    have h1 : (y : X) * z * (y : X)⁻¹ =
        ((y : X) * z₁ * (y : X)⁻¹) * ((y * t) * z₁ * (y * t)⁻¹) := by
      rw [hc.z_eq]
      group
    rw [h1]
    rcases hz₂ with h2 | h2 <;> rcases hz₂' with h3 | h3 <;> rw [h2, h3]
    · exfalso
      apply hc.z₁_ne
      have h4 : (y : X) * z₁ * (y : X)⁻¹ = (y * t) * z₁ * (y * t)⁻¹ := by rw [h2, h3]
      calc z₁ = (y : X)⁻¹ * ((y : X) * z₁ * (y : X)⁻¹) * y := by group
        _ = (y : X)⁻¹ * ((y * t) * z₁ * (y * t)⁻¹) * y := by rw [h4]
        _ = t * z₁ * t⁻¹ := by group
    · rw [hc.z_eq]
    · rw [hc.z_eq]
      exact hz₁₂.symm
    · exfalso
      apply hc.z₁_ne
      have h4 : (y : X) * z₁ * (y : X)⁻¹ = (y * t) * z₁ * (y * t)⁻¹ := by rw [h2, h3]
      calc z₁ = (y : X)⁻¹ * ((y : X) * z₁ * (y : X)⁻¹) * y := by group
        _ = (y : X)⁻¹ * ((y * t) * z₁ * (y * t)⁻¹) * y := by rw [h4]
        _ = t * z₁ * t⁻¹ := by group
  have hyβc : ∀ x ∈ W, (y : X) * β * (y : X)⁻¹ * x = x * ((y : X) * β * (y : X)⁻¹) := by
    intro x hx
    have hx' : (y : X)⁻¹ * x * y ∈ W := by
      have := (mem_normalizer_iff.mp (inv_mem hyN') x).mp hx
      rwa [inv_inv] at this
    have h1 := hc.comm_beta hx'
    calc (y : X) * β * (y : X)⁻¹ * x = y * (β * ((y : X)⁻¹ * x * y)) * (y : X)⁻¹ := by group
      _ = y * (((y : X)⁻¹ * x * y) * β) * (y : X)⁻¹ := by rw [h1]
      _ = x * ((y : X) * β * (y : X)⁻¹) := by group
  have hyβW : (y : X) * β * (y : X)⁻¹ ∈ W := (mem_normalizer_iff.mp hyN' β).mp
    (hc.T_le_W (hσ.X_le_T hs.beta.mem_X))
  have hyβ' : (y : X) * β * (y : X)⁻¹ = β * z := by
    rcases hc.mem_center_W hKC hyβW hyβc with h1 | h1 | h1 | h1
    · exfalso
      apply hs.beta_not_mem_zpowers_z
      have h2 : β = 1 := by
        calc β = (y : X)⁻¹ * ((y : X) * β * (y : X)⁻¹) * y := by group
          _ = 1 := by rw [h1]; group
      rw [← hβdef, h2]
      exact one_mem _
    · exfalso
      apply hyβ
      rw [mem_centralizer_singleton_iff]
      calc (y : X) * β = ((y : X) * β * (y : X)⁻¹) * y := by group
        _ = β * y := by rw [h1]
    · exfalso
      apply hs.beta_not_mem_zpowers_z
      have h2 : β = z := by
        calc β = (y : X)⁻¹ * ((y : X) * β * (y : X)⁻¹) * y := by group
          _ = (y : X)⁻¹ * ((y : X) * z * (y : X)⁻¹) * y := by rw [h1, hyz]
          _ = z := by group
      rw [← hβdef, h2]
      exact mem_zpowers z
    · exact h1
  have htβ : t * β = β * t := mem_centralizer_singleton_iff.mp (hW.le hc.t_mem_W)
  by_cases hyz₁ : (y : X) * z₁ = z₁ * y
  · exact ⟨Q, y, hQ, hWQ, y.2, hyN', hyz₁, hyz, hyβ'⟩
  · have hyt : (y : X) * t * z₁ = z₁ * ((y : X) * t) := by
      have h1 : (y : X) * z₁ * (y : X)⁻¹ ≠ z₁ := fun h2 => hyz₁ (by
        calc (y : X) * z₁ = (y * z₁ * (y : X)⁻¹) * y := by group
          _ = z₁ * y := by rw [h2])
      rcases hz₂' with h3 | h3
      · calc (y : X) * t * z₁ = ((y * t) * z₁ * (y * t)⁻¹) * (y * t) := by group
          _ = z₁ * ((y : X) * t) := by rw [h3]
      · exfalso
        rcases hz₂ with h2 | h2
        · exact h1 h2
        · apply hc.z₁_ne
          have h4 : (y : X) * z₁ * (y : X)⁻¹ = (y * t) * z₁ * (y * t)⁻¹ := by rw [h2, h3]
          calc z₁ = (y : X)⁻¹ * ((y : X) * z₁ * (y : X)⁻¹) * y := by group
            _ = (y : X)⁻¹ * ((y * t) * z₁ * (y * t)⁻¹) * y := by rw [h4]
            _ = t * z₁ * t⁻¹ := by group
    have htz : t * z = z * t := hc.comm_z hc.t_mem_W
    refine ⟨Q, y * t, hQ, hWQ, mul_mem y.2 (hWQ hc.t_mem_W),
      mul_mem hyN' (le_normalizer hc.t_mem_W), hyt, ?_, ?_⟩
    · calc (y : X) * t * z * ((y : X) * t)⁻¹ = (y : X) * (t * z) * t⁻¹ * (y : X)⁻¹ := by group
        _ = (y : X) * (z * t) * t⁻¹ * (y : X)⁻¹ := by rw [htz]
        _ = (y : X) * z * (y : X)⁻¹ := by group
        _ = z := hyz
    calc (y : X) * t * β * ((y : X) * t)⁻¹ = (y : X) * (t * β) * t⁻¹ * (y : X)⁻¹ := by group
      _ = (y : X) * (β * t) * t⁻¹ * (y : X)⁻¹ := by rw [htβ]
      _ = (y : X) * β * (y : X)⁻¹ := by group
      _ = β * z := hyβ'


theorem center_V (hKC : AutPSL2CentralizerInput) {𝒱 : Subgroup X} (h𝒱 : IsSylowOf 2 𝒱 ⊤)
    (hW𝒱 : W ≤ 𝒱) {τ : X} (hτ : τ ∈ 𝒱) (hτz : τ * z * τ⁻¹ = z)
    (hτβ : τ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * τ⁻¹ =
      w ^ (orderOf w / 2) * t ^ i * z ^ j * z) :
    (∀ c ∈ 𝒱, (∀ v ∈ 𝒱, c * v = v * c) → c = 1 ∨ c = z) ∧ ∀ v ∈ 𝒱, z * v = v * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ := hs.setup
  have hz1 := hσ.z_ne_one
  have hβW := hc.T_le_W (hσ.X_le_T hs.beta.mem_X)
  have h1 : ∀ c ∈ 𝒱, (∀ v ∈ 𝒱, c * v = v * c) → c = 1 ∨ c = z := by
    intro c hc𝒱 hcc
    have hcW : c ∈ W := by
      rw [← hc.inf_V_beta h𝒱 hW𝒱]
      exact mem_inf.mpr ⟨hc𝒱, mem_centralizer_singleton_iff.mpr (hcc _ (hW𝒱 hβW))⟩
    have hcτ := hcc τ hτ
    rcases hc.mem_center_W hKC hcW (fun y hy => hcc y (hW𝒱 hy)) with h2 | h2 | h2 | h2
    · exact Or.inl h2
    · exfalso
      apply hz1
      have h3 : τ * c * τ⁻¹ = c := by rw [← hcτ]; group
      rw [h2, hτβ] at h3
      calc z = (w ^ (orderOf w / 2) * t ^ i * z ^ j)⁻¹ *
          (w ^ (orderOf w / 2) * t ^ i * z ^ j * z) := by group
        _ = 1 := by rw [h3, inv_mul_cancel]
    · exact Or.inr h2
    · exfalso
      apply hz1
      have h3 : τ * c * τ⁻¹ = c := by rw [← hcτ]; group
      have h4 : τ * c * τ⁻¹ = (w ^ (orderOf w / 2) * t ^ i * z ^ j * z) * z := by
        rw [h2, show τ * (w ^ (orderOf w / 2) * t ^ i * z ^ j * z) * τ⁻¹ =
          (τ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * τ⁻¹) * (τ * z * τ⁻¹) by group, hτβ, hτz]
      rw [h3, h2] at h4
      calc z = (w ^ (orderOf w / 2) * t ^ i * z ^ j * z)⁻¹ *
          ((w ^ (orderOf w / 2) * t ^ i * z ^ j * z) * z) := by group
        _ = 1 := by rw [← h4, inv_mul_cancel]
  refine ⟨h1, ?_⟩
  have htV : t ∈ 𝒱 := hW𝒱 hc.t_mem_W
  have : Nontrivial ↥𝒱 := ⟨⟨⟨t, htV⟩, 1, fun h2 =>
    hs.standing.t_ne_one (congrArg Subtype.val h2)⟩⟩
  have hnt := h𝒱.isPGroup.center_nontrivial
  obtain ⟨c, hc1⟩ := exists_ne (1 : ↥(center ↥𝒱))
  have hcc : ∀ v ∈ 𝒱, ((c : ↥𝒱) : X) * v = v * c := fun v hv =>
    congrArg Subtype.val ((mem_center_iff.mp c.2) ⟨v, hv⟩).symm
  rcases h1 _ (c : ↥𝒱).2 hcc with h2 | h2
  · exact absurd (Subtype.ext (Subtype.ext h2)) hc1
  · intro v hv
    rw [← h2]
    exact (hcc v hv)

end Config415

end CFSG.ComponentClassification.HarrisLit
