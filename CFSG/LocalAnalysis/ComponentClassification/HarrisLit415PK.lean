module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PI
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Tools

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

namespace L415

theorem component_eq_of_layer_eq_sup {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hAB : A ⊔ B = layer G) (hc : A ≤ centralizer (B : Set G)) [IsSimpleGroup ↥A]
    [IsSimpleGroup ↥B] (hAn : ∃ a b : ↥A, a * b ≠ b * a) (hBn : ∃ a b : ↥B, a * b ≠ b * a)
    {J : Subgroup G} (hJ : IsComponent J) : J = A ∨ J = B := by
  have hE : (layer G).Normal := by
    have := LocalCores.layer_characteristic (G := G)
    infer_instance
  have hcB : B ≤ centralizer (A : Set G) := fun b hb =>
    mem_centralizer_iff.mpr fun a ha => (mem_centralizer_iff.mp (hc ha) b hb).symm
  have hsub : ∀ C D : Subgroup G, C ⊔ D = layer G → D ≤ centralizer (C : Set G) →
      C.IsSubnormal := by
    intro C D hCD hDC
    refine Subgroup.IsSubnormal.step C (layer G) (hCD ▸ le_sup_left) hE.isSubnormal ?_
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer (hCD ▸ le_sup_left)).mpr ?_
    rw [← hCD]
    exact sup_le le_normalizer (hDC.trans (centralizer_le_normalizer _))
  have hAs := hsub A B hAB hcB
  have hBs := hsub B A (by rw [sup_comm]; exact hAB) hc
  have hJn := LocalCores.isQuasisimple_nontrivial hJ.1
  have hJp : Group.IsPerfect ↥J := hJ.1.1
  have hin : ∀ C : Subgroup G, [IsSimpleGroup ↥C] → (∃ a b : ↥C, a * b ≠ b * a) → J ≤ C →
      J = C := by
    intro C _ hCn hJC
    have hq := LocalAnalysis.ComponentInitial.isQuasisimple_of_isSimpleGroup hCn
    have hsn := GorensteinWalter.isSubnormal_subgroupOf_of_subnormal_of_le hJC hJ.2
    rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hq hsn with h | h
    · refine le_antisymm hJC fun c hc => ?_
      have : (⟨c, hc⟩ : ↥C) ∈ J.subgroupOf C := by rw [h]; trivial
      exact this
    · exfalso
      rw [LocalAnalysis.ComponentInitial.center_eq_bot_of_isSimpleGroup hCn] at h
      have hJbot : J = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have h1 : (⟨x, hJC hx⟩ : ↥C) ∈ J.subgroupOf C := hx
        have h2 := h h1
        rw [mem_bot] at h2
        exact (mem_bot).mpr (congrArg Subtype.val h2)
      exact ((Subgroup.nontrivial_iff_ne_bot J).mp hJn) hJbot
  rcases LocalCores.component_subnormal_subgroup hJ hAs with hJA | hJA
  · exact Or.inl (hin A hAn hJA)
  rcases LocalCores.component_subnormal_subgroup hJ hBs with hJB | hJB
  · exact Or.inr (hin B hBn hJB)
  exfalso
  rw [commutator_eq_bot_iff_le_centralizer] at hJA hJB
  have hJE : J ≤ layer G := LocalCores.component_le_layer hJ
  have hJc : ∀ x ∈ J, ∀ y ∈ J, x * y = y * x := by
    intro x hx y hy
    have hle : A ⊔ B ≤ centralizer ({x} : Set G) := sup_le
      (fun a ha => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hJA hx) a ha))
      (fun b hb => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hJB hx) b hb))
    rw [hAB] at hle
    exact (mem_centralizer_singleton_iff.mp (hle (hJE hy))).symm
  have hcomm : commutator ↥J = ⊥ := by
    rw [_root_.commutator_def, commutator_eq_bot_iff_le_centralizer]
    intro x _
    exact mem_centralizer_iff.mpr fun y _ => Subtype.ext (hJc y y.2 x x.2)
  rw [hJp.commutator_eq_top] at hcomm
  have := hJn
  obtain ⟨a, b, hab⟩ := exists_pair_ne ↥J
  apply hab
  have h1 : a ∈ (⊤ : Subgroup ↥J) := mem_top a
  have h2 : b ∈ (⊤ : Subgroup ↥J) := mem_top b
  rw [hcomm, mem_bot] at h1 h2
  rw [h1, h2]

end L415

variable {X : Type} [Group X] [Finite X]
  {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X} {w z : X} {V : Subgroup X}
  {i j : ℕ} {z₁ τ α : X} {K₂ W 𝒱 : Subgroup X}

namespace Data415B

variable (hD : Data415B t L p f S w z V i j z₁ τ α K₂ W 𝒱)
include hD

theorem K₂F_lt {M : Subgroup (MBar z₁)} (hKM : barOf (centralizer {z₁}) K₂ ≤ M)
    (hinv : ∀ v : MBar z₁, v * QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ =
      QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ * v → M.map (MulAut.conj v).toMonoidHom = M) :
    barOf (centralizer {z₁}) K₂ < M := by
  refine lt_of_le_of_ne hKM fun heq => ?_
  obtain ⟨hKb, -, -⟩ := L415.isPComponent_barOf hD.beta_mem_F hD.orderOf_beta
    hD.fd.isTwoComponentIn_K₂
  have hτF : τ ∈ centralizer ({z₁} : Set X) := (mem_inf.mp hD.fd.τ_mem).2
  have hzF : z ∈ centralizer ({z₁} : Set X) := (mem_inf.mp hD.z_mem_center.1).2
  have hz₁F : z₁ ∈ centralizer ({z₁} : Set X) := mem_centralizer_singleton_iff.mpr rfl
  set τb : MBar z₁ := QuotientGroup.mk ⟨τ, hτF⟩ with hτb
  have hτz₂ := hD.V₀F_comm_z₂F (mk_mem_barOf hτF hD.fd.τ_mem)
  have hmapτ := hinv τb hτz₂
  have hconj : ∀ k ∈ barOf (centralizer {z₁}) K₂, τb⁻¹ * k * τb ∈ barOf (centralizer {z₁}) K₂ := by
    intro k hk
    rw [heq] at hk ⊢
    rw [← hmapτ] at hk
    obtain ⟨y, hy, rfl⟩ := hk
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show τb⁻¹ * (τb * y * τb⁻¹) * τb = y by group]
    exact hy
  have hτβ : τb * QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hD.beta_mem_F⟩ * τb⁻¹ =
      QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hD.beta_mem_F⟩ *
        QuotientGroup.mk ⟨z, hzF⟩ := by
    rw [hτb, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hD.fd.τ_conj
  have hz : (QuotientGroup.mk ⟨z, hzF⟩ : MBar z₁) =
      QuotientGroup.mk ⟨z₁, hz₁F⟩ * QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ := by
    rw [← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hD.fd.z_eq
  have hz₁c : ∀ k : MBar z₁, k * QuotientGroup.mk ⟨z₁, hz₁F⟩ =
      QuotientGroup.mk ⟨z₁, hz₁F⟩ * k := by
    intro k
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp k.2)
  obtain ⟨k, hk, hkz⟩ := hD.exists_not_comm_z₂F
  apply hkz
  have hkb := mem_centralizer_singleton_iff.mp (hKb hk)
  have hk' := mem_centralizer_singleton_iff.mp (hKb (hconj k hk))
  set bb : MBar z₁ := QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hD.beta_mem_F⟩
  set zb : MBar z₁ := QuotientGroup.mk ⟨z, hzF⟩
  have h1 : k * (bb * zb) = (bb * zb) * k := by
    rw [← hτβ]
    calc k * (τb * bb * τb⁻¹) = τb * ((τb⁻¹ * k * τb) * bb) * τb⁻¹ := by group
      _ = τb * (bb * (τb⁻¹ * k * τb)) * τb⁻¹ := by rw [hk']
      _ = τb * bb * τb⁻¹ * k := by group
  have h2 : k * zb = zb * k := by
    calc k * zb = bb⁻¹ * (k * bb) * zb := by
          rw [show bb⁻¹ * (k * bb) * zb = bb⁻¹ * (bb * k) * zb by rw [hkb]]; group
      _ = bb⁻¹ * (k * (bb * zb)) := by group
      _ = bb⁻¹ * ((bb * zb) * k) := by rw [h1]
      _ = zb * k := by group
  rw [hz] at h2
  have h3 := hz₁c k
  calc k * QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ =
      (QuotientGroup.mk ⟨z₁, hz₁F⟩)⁻¹ * (k * (QuotientGroup.mk ⟨z₁, hz₁F⟩ *
        QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩)) := by
          rw [← mul_assoc k, h3]; group
    _ = (QuotientGroup.mk ⟨z₁, hz₁F⟩)⁻¹ * ((QuotientGroup.mk ⟨z₁, hz₁F⟩ *
        QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩) * k) := by rw [h2]
    _ = QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ * k := by group

theorem card_KBar_le : Nat.card ↥(Standing.Setup42.KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤
    Nat.card ↥(barOf (centralizer {z₁}) K₂) := by
  obtain ⟨e⟩ := hD.nonempty_K₂F_equiv
  rw [← Nat.card_congr e.toEquiv]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (pPrimeCore 2 ↥(barOf (centralizer {z₁}) K₂))
  have h2 : 0 < Nat.card ↥(pPrimeCore 2 ↥(barOf (centralizer {z₁}) K₂)) := Nat.card_pos
  rw [h1]
  exact Nat.le_mul_of_pos_right _ h2

theorem not_conj_beta {M : Subgroup (MBar z₁)} (hM : IsComponent M)
    (hlt : barOf (centralizer {z₁}) K₂ < M) (g : X) :
    g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g⁻¹ ≠ z₁ := by
  intro hg
  have hCC : (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)).map
      (MulAut.conj g).toMonoidHom = centralizer ({z₁} : Set X) := by
    rw [L415.map_conj_centralizer, hg]
  obtain ⟨e⟩ : Nonempty (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ≃* MBar z₁) :=
    ⟨UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (((centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)).equivMapOfInjective _
        (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hCC))⟩
  have hJ : IsComponent (M.map e.symm.toMonoidHom) := LocalCores.isComponent_map_mulEquiv e.symm hM
  obtain ⟨hq, -⟩ | ⟨A, B, hsup, -, hcen, -, ⟨eA⟩, ⟨eB⟩, hlie, -, -⟩ := hD.h412.lemma46d
  · exact hD.hnq hq
  obtain ⟨hs, hnab⟩ := L415.simple_nonabelian_of_lieModel hlie
  have : IsSimpleGroup ↥A := eA.isSimpleGroup
  have : IsSimpleGroup ↥B := eB.isSimpleGroup
  have hAn : ∃ a b : ↥A, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨eA.symm a, eA.symm b, fun h => hab (by simpa using congrArg eA h)⟩
  have hBn : ∃ a b : ↥B, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨eB.symm a, eB.symm b, fun h => hab (by simpa using congrArg eB h)⟩
  have hcard : Nat.card M =
      Nat.card ↥(Standing.Setup42.KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    rw [← Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective]
    rcases L415.component_eq_of_layer_eq_sup hsup hcen hAn hBn hJ with h | h <;> rw [h]
    · exact Nat.card_congr eA.toEquiv
    · exact Nat.card_congr eB.toEquiv
  have h1 := Subgroup.card_lt_of_lt hlt
  have h2 := hD.card_KBar_le
  exact absurd h1 (not_lt.mpr (hcard.le.trans h2))

theorem relIndex_W₀F_le_two (hnβ : ∀ g : X, g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g⁻¹ ≠ z₁) :
    (barOf (centralizer {z₁})
      (𝒱 ⊓ centralizer {z₁} ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})).relIndex
      (barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁})) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, h2⟩ := hD.fd.fusion hnβ
  have hV₀ : Nat.card ↥(𝒱 ⊓ centralizer ({z₁} : Set X)) =
      twoPart (centralizer ({z₁} : Set X)) := hD.fd.isSylowOf_𝒱₀.card_eq
  have hW : Nat.card W = twoPart (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) :=
    hD.fd.isSylowOf_W.card_eq
  have hW₀ := hD.fd.card_W₀
  have hp : IsPGroup 2 ↥(𝒱 ⊓ centralizer ({z₁} : Set X)) :=
    hD.fd.isSylowOf_𝒱.isPGroup.to_le inf_le_left
  have h1 := Subgroup.relIndex_mul_card (barOf (centralizer {z₁})
    (𝒱 ⊓ centralizer {z₁} ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}))
    (barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}))
  rw [inf_of_le_left W₀F_le_V₀F, card_barOf inf_le_right hp,
    card_barOf (inf_le_left.trans inf_le_right) (hp.to_le inf_le_left)] at h1
  have hpos : 0 < Nat.card ↥(𝒱 ⊓ centralizer {z₁} ⊓
      centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) := Nat.card_pos
  by_contra h3
  push Not at h3
  have h4 : 3 * Nat.card ↥(𝒱 ⊓ centralizer {z₁} ⊓
      centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) ≤ _ := Nat.mul_le_mul_right _ h3
  omega

end Data415B

end CFSG.ComponentClassification.HarrisLit
