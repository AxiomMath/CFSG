module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415W0
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Tools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndTransfer
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma43

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd


variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ} {hs : Setting46e t L p f S w z V i j}
  {Kb₁ Kb₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} {W : Subgroup X} {z₁ : X}

namespace Config415

variable (hc : Config415 hs Kb₁ Kb₂ W z₁)
include hc

theorem beta_not_mem :
    w ^ (orderOf w / 2) * t ^ i * z ^ j ∉ zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹) := by
  set M := centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)
  have hWM : W ≤ M := hc.isSylowOf_W.le
  have hE : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := by
    have := LocalCores.layer_characteristic (G := MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    infer_instance
  have htM : t ∈ M := hc.isSylowOf_W.le hc.t_mem_W
  have hz₁M : z₁ ∈ M := hWM hc.z₁_mem
  set P := preimageOf M (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
  have hz₁P : z₁ ∈ P := (mem_preimageOf hz₁M).mpr (hc.prod.K₁_le (hc.mk_z₁ hz₁M))
  have hz₂P : t * z₁ * t⁻¹ ∈ P := by
    have hz₂M : t * z₁ * t⁻¹ ∈ M := mul_mem (mul_mem htM hz₁M) (inv_mem htM)
    refine (mem_preimageOf hz₂M).mpr ?_
    have h1 := hE.conj_mem _ (hc.prod.K₁_le (hc.mk_z₁ hz₁M)) (QuotientGroup.mk ⟨t, htM⟩)
    exact h1
  intro hβ
  have hβP : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ P :=
    (sup_le ((zpowers_le).mpr hz₁P) ((zpowers_le).mpr hz₂P)) hβ
  have hβM : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ M := mem_centralizer_singleton_iff.mpr rfl
  have hβE := (mem_preimageOf hβM).mp hβP
  apply hs.betaBar_ne_one
  refine hc.prod.eq_one_of_mem_centralizer hβE (mem_centralizer_iff.mpr fun y _ => ?_)
  exact ((mem_center_iff.mp (betaBar_mem_center _)) y)

omit hc in
theorem card_center_S_le (hs : Setting46e t L p f S w z V i j)
    (hne : S ≠ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) :
    Nat.card ↥(S ⊓ centralizer (S : Set X)) ≤ 4 := by
  have h41 := (hs.standing.lemma41_of_lift hs.sylow hs.setup.lift hs.setup.gen3).2.2.2.2.2.2.2.1
    hne
  rw [h41, hs.setup.center_D]
  have hzt : t * z = z * t :=
    (mem_centralizer_singleton_iff.mp (hs.sylow.le hs.setup.z_mem.1)).symm
  have hc' : ∀ a ∈ zpowers t, ∀ b ∈ zpowers z, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨l, rfl⟩ := mem_zpowers_iff.mp hb
    exact ((Commute.zpow_right hzt l).zpow_left k)
  obtain ⟨hcard, -⟩ := GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc'
  have ht2 : t * t = 1 := by rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]
  have hz2 : z * z = 1 := by rw [← sq, ← hs.setup.z_order, pow_orderOf_eq_one]
  have h1 : Nat.card (zpowers t) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact ht2))
  have h2 : Nat.card (zpowers z) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hz2))
  have hpos : 0 < Nat.card ↥(zpowers t ⊓ zpowers z) := Nat.card_pos
  have h3 : Nat.card ↥(zpowers t ⊔ zpowers z) ≤
      Nat.card ↥(zpowers t ⊔ zpowers z) * Nat.card ↥(zpowers t ⊓ zpowers z) :=
    Nat.le_mul_of_pos_right _ hpos
  calc Nat.card ↥(zpowers t ⊔ zpowers z) ≤ Nat.card (zpowers t) * Nat.card (zpowers z) :=
        h3.trans hcard.le
    _ ≤ 2 * 2 := Nat.mul_le_mul h1 h2
    _ = 4 := by norm_num

omit hc in
theorem card_center_sylow_le (hs : Setting46e t L p f S w z V i j)
    (hne : S ≠ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) (g : X)
    {P : Subgroup X} (hP : IsSylowOf 2 P (centralizer {g⁻¹ * t * g})) :
    Nat.card ↥(P ⊓ centralizer (P : Set X)) ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP₁ := HarrisLit.isSylowOf_map (MulAut.conj g).toMonoidHom hP
  rw [L415.map_conj_centralizer, show g * (g⁻¹ * t * g) * g⁻¹ = t by group] at hP₁
  obtain ⟨k, -, hk⟩ := L415.exists_map_conj hs.sylow hP₁
  have hZ1 : Nat.card ↥(P ⊓ centralizer (P : Set X)) =
      Nat.card ↥(P.map (MulAut.conj g).toMonoidHom ⊓
        centralizer ((P.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X)) := by
    rw [← L415.map_conj_inf_centralizer P g,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hZ2 : Nat.card ↥(P.map (MulAut.conj g).toMonoidHom ⊓
      centralizer ((P.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X)) =
        Nat.card ↥(S ⊓ centralizer (S : Set X)) := by
    rw [hk, ← L415.map_conj_inf_centralizer S k,
      Subgroup.card_map_of_injective (MulAut.conj k).injective]
  rw [hZ1, hZ2]
  exact card_center_S_le hs hne

theorem S_eq_T (g : X) (hτW₀ : g⁻¹ * t * g ∈ W ⊓ centralizer {z₁})
    (hτSyl : IsSylowOf 2 (W ⊓ centralizer {g⁻¹ * t * g}) (centralizer {g⁻¹ * t * g})) :
    S = zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
  by_contra hne
  have h4 := card_center_sylow_le hs hne g hτSyl
  have hσ := hs.setup
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβdef
  set τ := g⁻¹ * t * g with hτdef
  have ht2 : t * t = 1 := by rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]
  have hτ2 : τ * τ = 1 := by
    rw [hτdef, show g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group, ht2]; group
  have hτnot : ¬ (W ⊓ centralizer {z₁} ≤ centralizer {τ}) := by
    have := hc.not_le_centralizer_conj g⁻¹
    rwa [inv_inv] at this
  have hz2 : z * z = 1 := by rw [← sq, ← hσ.z_order, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := fun h1 => by
    have := hσ.z_order
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hβ2 : β * β = 1 := by rw [← sq]; exact hσ.sq_eq_one_of_mem_X hs.beta.mem_X
  have hβz : β ∉ zpowers z := by
    intro h1
    rcases L415.mem_zpowers_two hz2 h1 with h2 | h2
    · exact hs.beta.ne_one h2
    · exact Standing.Setup42.beta_ne_z hσ hs.beta h2
  have hzW : z ∈ W := hc.T_le_W (mem_sup_left (mem_sup_right hσ.z_mem))
  have hβW : β ∈ W := hc.T_le_W (hσ.X_le_T hs.beta.mem_X)
  have hτW : τ ∈ W := hτW₀.1
  obtain ⟨hA₁c, hA₁2⟩ := L415.elem_zpowers hz2
  obtain ⟨hA₂c, hA₂2, hA₂⟩ := L415.elem_sup hA₁c hA₁2 hβ2 hβz (fun a ha => by
    rcases L415.mem_zpowers_two hz2 ha with rfl | rfl
    · simp
    · exact (hc.comm_beta hzW))
  have hA₂W₀ : zpowers z ⊔ zpowers β ≤ centralizer ((W ⊓ centralizer {z₁} : Subgroup X) : Set X) :=
    sup_le (zpowers_le.mpr (mem_centralizer_iff.mpr fun x hx => hc.comm_z hx.1))
      (zpowers_le.mpr (mem_centralizer_iff.mpr fun x hx => hc.comm_beta hx.1))
  have hτA₂ : τ ∉ zpowers z ⊔ zpowers β := fun h1 =>
    hτnot fun x hx => mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hA₂W₀ h1)) x hx)
  obtain ⟨-, -, hA₃⟩ := L415.elem_sup hA₂c hA₂2 hτ2 hτA₂ (fun a ha =>
    ((mem_centralizer_iff.mp (hA₂W₀ ha)) τ hτW₀).symm)
  rw [hA₂, L415.card_zpowers_two hz2 hz1] at hA₃
  have hle : zpowers z ⊔ zpowers β ⊔ zpowers τ ≤ (W ⊓ centralizer {τ}) ⊓
      centralizer ((W ⊓ centralizer {τ} : Subgroup X) : Set X) := by
    refine sup_le (sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)) (zpowers_le.mpr ?_)
    · exact mem_inf.mpr ⟨mem_inf.mpr ⟨hzW, mem_centralizer_singleton_iff.mpr (hc.comm_z hτW).symm⟩,
        mem_centralizer_iff.mpr fun x hx => hc.comm_z (mem_inf.mp hx).1⟩
    · exact mem_inf.mpr ⟨mem_inf.mpr ⟨hβW, mem_centralizer_singleton_iff.mpr
        (hc.comm_beta hτW).symm⟩,
        mem_centralizer_iff.mpr fun x hx => hc.comm_beta (mem_inf.mp hx).1⟩
    · exact mem_inf.mpr ⟨mem_inf.mpr ⟨hτW, mem_centralizer_singleton_iff.mpr rfl⟩,
        mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2⟩
  have h8 := Subgroup.card_le_of_le hle
  rw [hA₃] at h8
  omega

theorem not_isSylowOf [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKC : AutPSL2CentralizerInput) : ¬ IsSylowOf 2 W ⊤ := by
  intro hWs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ := hs.setup
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβdef
  set T := zpowers t ⊔ (S ⊓ L) ⊔ zpowers w with hTdef
  have htW := hc.t_mem_W
  have ht2 : t * t = 1 := by rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]
  have htW₀ : t ∉ W ⊓ centralizer {z₁} := fun h1 =>
    hc.t_not_comm (mem_centralizer_singleton_iff.mp h1.2)
  have hWp : IsPGroup 2 W := hWs.isPGroup
  have hWidx : ¬ 2 ∣ W.index := by
    have := (isSylowOf_iff.mp hWs).2.2
    rwa [Subgroup.relIndex_top_right] at this
  obtain ⟨g, hgW₀, hext, hgc⟩ := HarrisEnd.exists_extremal_conj_of_relIndex_two hnab hWp hWidx
    inf_le_left hc.relIndex_W₀ htW htW₀ (by rw [sq]; exact ht2)
  set τ := g⁻¹ * t * g with hτdef
  have hτSyl : IsSylowOf 2 (W ⊓ centralizer {τ}) (centralizer {τ}) := isSylowOf_iff.mpr hext
  have hST := hc.S_eq_T g hgW₀ hτSyl
  have hcardC : Nat.card ↥(W ⊓ centralizer {τ}) = Nat.card S := by
    rw [hτSyl.card_eq, ← show (centralizer ({t} : Set X)).map (MulAut.conj g⁻¹).toMonoidHom =
      centralizer {τ} by rw [L415.map_conj_centralizer, inv_inv],
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, ← hs.sylow.card_eq]
  have hCWt := hσ.inf_W_t hKC hs.beta hc.isSylowOf_W hc.U_le
  have hTg : T.map (MulAut.conj g⁻¹).toMonoidHom ≤ W ⊓ centralizer {τ} := by
    rintro _ ⟨c, hcT, rfl⟩
    have h1 := hgc c (hCWt ▸ hcT)
    simpa [MulAut.conj_apply] using h1
  have hCW : W ⊓ centralizer {τ} = T.map (MulAut.conj g⁻¹).toMonoidHom := by
    refine (eq_of_le_of_card_ge hTg ?_).symm
    rw [hcardC, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact le_of_eq (congrArg (fun H : Subgroup X => Nat.card H) hST)
  set T₀ := W ⊓ centralizer {z₁} ⊓ centralizer {τ} with hT₀
  have hT₀le : T₀ ≤ W ⊓ centralizer {τ} := inf_le_inf_right _ inf_le_left
  have hnorm : ∀ c ∈ W ⊓ centralizer {τ}, ∀ y ∈ T₀, c * y * c⁻¹ ∈ T₀ := by
    intro c hc' y hy
    refine mem_inf.mpr ⟨hc.conj_mem_W₀ (mem_inf.mp hc').1 (mem_inf.mp hy).1, ?_⟩
    have h1 : c * τ = τ * c := mem_centralizer_singleton_iff.mp (mem_inf.mp hc').2
    have h2 : y * τ = τ * y := mem_centralizer_singleton_iff.mp (mem_inf.mp hy).2
    rw [mem_centralizer_singleton_iff]
    calc c * y * c⁻¹ * τ = c * y * (c⁻¹ * τ) := by group
      _ = c * y * (τ * c⁻¹) := by
          rw [show c⁻¹ * τ = τ * c⁻¹ by
            calc c⁻¹ * τ = c⁻¹ * (τ * c) * c⁻¹ := by group
              _ = c⁻¹ * (c * τ) * c⁻¹ := by rw [h1]
              _ = τ * c⁻¹ := by group]
      _ = c * (y * τ) * c⁻¹ := by group
      _ = c * (τ * y) * c⁻¹ := by rw [h2]
      _ = (c * τ) * y * c⁻¹ := by group
      _ = τ * (c * y * c⁻¹) := by rw [h1]; group
  have hτnot : ¬ (W ⊓ centralizer {z₁} ≤ centralizer {τ}) := by
    have := hc.not_le_centralizer_conj g⁻¹
    rwa [inv_inv] at this
  have hτ2 : τ * τ = 1 := by
    rw [hτdef, show g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group, ht2]; group
  have hz₁2 : z₁ * z₁ = 1 := by rw [← sq]; exact hc.sq_z₁
  have hz₁1 : z₁ ≠ 1 := fun h1 => hc.z₁_ne (by rw [h1]; group)
  have hz₂2 : (t * z₁ * t⁻¹) * (t * z₁ * t⁻¹) = 1 := by
    rw [show t * z₁ * t⁻¹ * (t * z₁ * t⁻¹) = t * (z₁ * z₁) * t⁻¹ by group, hz₁2]; group
  have hz₂1 : t * z₁ * t⁻¹ ≠ 1 := fun h1 => hz₁1 (by
    calc z₁ = t⁻¹ * (t * z₁ * t⁻¹) * t := by group
      _ = 1 := by rw [h1]; group)
  have hz₁W := hc.z₁_mem
  have hz₂W : t * z₁ * t⁻¹ ∈ W := mul_mem (mul_mem htW hz₁W) (inv_mem htW)
  have hβW : β ∈ W := hc.T_le_W (hσ.X_le_T hs.beta.mem_X)
  have hβ2 : β * β = 1 := by rw [← sq]; exact hσ.sq_eq_one_of_mem_X hs.beta.mem_X
  have hz₁₂ : z₁ * (t * z₁ * t⁻¹) = (t * z₁ * t⁻¹) * z₁ := by
    have h1 := hc.comm_z hz₁W
    rw [hc.z_eq] at h1
    have h2 : t * z₁ * t⁻¹ = z₁ * (t * z₁ * t⁻¹) * z₁ := by
      calc t * z₁ * t⁻¹ = (z₁ * z₁) * (t * z₁ * t⁻¹) := by rw [hz₁2, one_mul]
        _ = z₁ * (z₁ * (t * z₁ * t⁻¹)) := by group
        _ = z₁ * (t * z₁ * t⁻¹) * z₁ := h1
    calc z₁ * (t * z₁ * t⁻¹) = z₁ * (z₁ * (t * z₁ * t⁻¹) * z₁) := by rw [← h2]
      _ = (z₁ * z₁) * (t * z₁ * t⁻¹) * z₁ := by group
      _ = (t * z₁ * t⁻¹) * z₁ := by rw [hz₁2, one_mul]
  have hW₀z₁ : z₁ ∈ centralizer ((W ⊓ centralizer {z₁} : Subgroup X) : Set X) :=
    mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2
  have hW₀z₂ : t * z₁ * t⁻¹ ∈ centralizer ((W ⊓ centralizer {z₁} : Subgroup X) : Set X) :=
    mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (hc.W₀_le_z₂ hx)
  have hW₀β : β ∈ centralizer ((W ⊓ centralizer {z₁} : Subgroup X) : Set X) :=
    mem_centralizer_iff.mpr fun x hx => hc.comm_beta (mem_inf.mp hx).1
  obtain ⟨hB₁c, hB₁2⟩ := L415.elem_zpowers hz₁2
  have hz₂B₁ : t * z₁ * t⁻¹ ∉ zpowers z₁ := fun h1 => by
    rcases L415.mem_zpowers_two hz₁2 h1 with h2 | h2
    · exact hz₂1 h2
    · exact hc.z₁_ne h2.symm
  obtain ⟨hB₂c, hB₂2, hB₂⟩ := L415.elem_sup hB₁c hB₁2 hz₂2 hz₂B₁ (fun a ha => by
    rcases L415.mem_zpowers_two hz₁2 ha with rfl | rfl
    · simp
    · exact hz₁₂)
  have hB₂W : zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹) ≤ W :=
    sup_le (zpowers_le.mpr hz₁W) (zpowers_le.mpr hz₂W)
  obtain ⟨hB₃c, hB₃2, hB₃⟩ := L415.elem_sup hB₂c hB₂2 hβ2 hc.beta_not_mem (fun a ha =>
    hc.comm_beta (hB₂W ha))
  have hB₃W₀ : zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹) ⊔ zpowers β ≤
      centralizer ((W ⊓ centralizer {z₁} : Subgroup X) : Set X) :=
    sup_le (sup_le (zpowers_le.mpr hW₀z₁) (zpowers_le.mpr hW₀z₂)) (zpowers_le.mpr hW₀β)
  have hτB₃ : τ ∉ zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹) ⊔ zpowers β := fun h1 =>
    hτnot fun x hx => mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hB₃W₀ h1)) x hx)
  obtain ⟨-, hB₄2, hB₄⟩ := L415.elem_sup hB₃c hB₃2 hτ2 hτB₃ (fun a ha =>
    ((mem_centralizer_iff.mp (hB₃W₀ ha)) τ hgW₀).symm)
  rw [hB₃, hB₂, L415.card_zpowers_two hz₁2 hz₁1] at hB₄
  have hτW : τ ∈ W := (mem_inf.mp hgW₀).1
  have hz₁T₀ : z₁ ∈ T₀ := mem_inf.mpr ⟨mem_inf.mpr ⟨hz₁W, mem_centralizer_singleton_iff.mpr rfl⟩,
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (mem_inf.mp hgW₀).2).symm⟩
  have hz₂T₀ : t * z₁ * t⁻¹ ∈ T₀ := mem_inf.mpr ⟨mem_inf.mpr ⟨hz₂W,
    mem_centralizer_singleton_iff.mpr hz₁₂.symm⟩,
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hc.W₀_le_z₂ hgW₀)).symm⟩
  have hβT₀ : β ∈ T₀ := mem_inf.mpr ⟨mem_inf.mpr ⟨hβW,
    mem_centralizer_singleton_iff.mpr (hc.comm_beta hz₁W).symm⟩,
    mem_centralizer_singleton_iff.mpr (hc.comm_beta hτW).symm⟩
  have hτT₀ : τ ∈ T₀ := mem_inf.mpr ⟨hgW₀, mem_centralizer_singleton_iff.mpr rfl⟩
  have hT₀W₀ : T₀ ≤ W ⊓ centralizer {z₁} := inf_le_left
  have hcen : centralizer ((W ⊓ centralizer {z₁} : Subgroup X) : Set X) ≤
      centralizer ((T₀ : Subgroup X) : Set X) := Subgroup.centralizer_le hT₀W₀
  have hB₄T₀ : zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹) ⊔ zpowers β ⊔ zpowers τ ≤ T₀ :=
    sup_le (sup_le (sup_le (zpowers_le.mpr hz₁T₀) (zpowers_le.mpr hz₂T₀))
      (zpowers_le.mpr hβT₀)) (zpowers_le.mpr hτT₀)
  have hB₄c : zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹) ⊔ zpowers β ⊔ zpowers τ ≤
      centralizer ((T₀ : Subgroup X) : Set X) :=
    sup_le (sup_le (sup_le (zpowers_le.mpr (hcen hW₀z₁)) (zpowers_le.mpr (hcen hW₀z₂)))
      (zpowers_le.mpr (hcen hW₀β)))
      (zpowers_le.mpr (mem_centralizer_iff.mpr fun y hy =>
        mem_centralizer_singleton_iff.mp (mem_inf.mp hy).2))
  have hB₄Z : zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹) ⊔ zpowers β ⊔ zpowers τ ≤ L415.centralInv T₀ :=
    fun x hx => ⟨hB₄T₀ hx, fun y hy => ((mem_centralizer_iff.mp (hB₄c hx)) y hy).symm,
      hB₄2 x hx⟩
  have h16 : 16 ≤ Nat.card ↥(L415.centralInv T₀) := by
    have := Subgroup.card_le_of_le hB₄Z
    rw [hB₄] at this
    omega
  set Z' := (L415.centralInv T₀).map (MulAut.conj g).toMonoidHom with hZ'
  have hZ'T : Z' ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ T.map (MulAut.conj g⁻¹).toMonoidHom := hCW ▸ hT₀le hx.1
    obtain ⟨y, hy, rfl⟩ := hx'
    simpa [MulAut.conj_apply, mul_assoc] using hy
  have hZ'n : ∀ d ∈ S ⊓ L, ∀ y ∈ Z', d * y * d⁻¹ ∈ Z' := by
    rintro d hd _ ⟨x, hx, rfl⟩
    have hdT : d ∈ T := mem_sup_left (mem_sup_right hd)
    have hcW : g⁻¹ * d * g ∈ W ⊓ centralizer {τ} := by
      rw [hCW]
      exact ⟨d, hdT, by simp⟩
    have hciW : (g⁻¹ * d * g)⁻¹ ∈ W ⊓ centralizer {τ} := inv_mem hcW
    have h1 := L415.conj_mem_centralInv (hnorm _ hcW) (fun y hy => by
      have := hnorm _ hciW y hy
      rwa [inv_inv] at this) hx
    refine ⟨_, h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hZ'2 : ∀ x ∈ Z', x ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [sq, show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, hx.2.2]
    group
  have hZ'X := hσ.le_X_of_normal_T hZ'T hZ'n hZ'2
  have h8 := Subgroup.card_le_of_le hZ'X
  rw [hσ.card_X, hZ', Subgroup.card_map_of_injective (MulAut.conj g).injective] at h8
  omega

end Config415

end CFSG.ComponentClassification.HarrisLit
