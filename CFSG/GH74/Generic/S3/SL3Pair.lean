module

public import CFSG.GH74.Generic.S3.Prop21Leaves

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups

@[expose] def B_L3_cover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ), p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    ∀ L : Subgroup G, IsQuasisimple ↥L → Odd (Nat.card ↥(center ↥L)) →
      (LieModel (↥L ⧸ center ↥L) .PSL 3 p f →
        ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f →
          ∃ α : SL(3, F) →* G, α.ker ≤ Subgroup.center SL(3, F) ∧ α.range = L) ∧
      (LieModel (↥L ⧸ center ↥L) .PSU 3 p f →
        ∀ (F₂ : Type) (_ : Field F₂) (_ : Finite F₂), Nat.card F₂ = (p ^ f) ^ 2 →
          ∃ α : ↥(StatedSU 3 (p ^ f) F₂) →* G,
            α.ker ≤ Subgroup.center ↥(StatedSU 3 (p ^ f) F₂) ∧ α.range = L)

@[expose] def B_S3_J_contain : Prop :=
  ∀ (G : Type) [Group G] [Finite G], GlobalHyp G →
    ∀ (t : StatedLieTag) (p f : ℕ) (v w : G) (Iv Iw Ivw P V : Subgroup G) (v₁ : G),
      Config22 G t p f v w Iv Iw Ivw P V v₁ →
      ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f →
        ∀ J₀ J₁ J₂ : Subgroup G, IsSL2Comp F w v J₀ → IsSL2Comp F w v₁ J₁ →
          IsSL2Comp F (w * v₁) v J₂ →
          J₀ ≤ Iw ∧ J₁ ≤ Iw ∧
            ∃ g : G, J₁ ≤ Iw.map (MulAut.conj g).toMonoidHom ∧ J₂ ≤ Iw.map (MulAut.conj g).toMonoidHom

@[expose] def B_S3_J_in_Iw : Prop :=
  ∀ (G : Type) [Group G] [Finite G], GlobalHyp G →
    ∀ (t : StatedLieTag) (p f : ℕ) (v w : G) (Iv Iw Ivw P V : Subgroup G) (v₁ : G),
      Config22 G t p f v w Iv Iw Ivw P V v₁ →
      ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f →
        ∀ e ∈ Vsharp V, ∀ J : Subgroup G, IsSL2Comp F w e J → J ≤ Iw

section Transport

variable {A B X G : Type*} [Group A] [Group B] [Group X] [Group G]

theorem exists_hom_of_mulEquiv (e : A ≃* B) (θ : A →* X) (hker : θ.ker ≤ center A) :
    ∃ θ' : B →* X, θ'.ker ≤ center B ∧ θ'.range = θ.range := by
  refine ⟨θ.comp e.symm.toMonoidHom, fun x hx => ?_, ?_⟩
  · have h1 : θ (e.symm x) = 1 := hx
    have h2 : e.symm x ∈ center A := hker (MonoidHom.mem_ker.mpr h1)
    have h3 : e (e.symm x) ∈ Set.center B := (MulEquivClass.apply_mem_center_iff e).2 h2
    rw [MulEquiv.apply_symm_apply] at h3
    exact h3
  · ext y
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨e.symm b, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨e a, by simp⟩

theorem exists_hom_conj (α : A →* G) (hker : α.ker ≤ center A) (g : G) :
    ∃ α' : A →* G, α'.ker ≤ center A ∧ α'.range = α.range.map (MulAut.conj g).toMonoidHom := by
  refine ⟨(MulAut.conj g).toMonoidHom.comp α, fun x hx => hker ?_, ?_⟩
  · have h1 : g * α x * g⁻¹ = 1 := hx
    rw [MonoidHom.mem_ker]
    simpa using h1
  · rw [MonoidHom.range_comp]

end Transport

section Pairs

variable {G : Type} [Group G]

theorem linear_pair_sup {K : Type} [Field K] [Finite K] (hK4 : 4 ≤ Nat.card K) (h2 : (2 : K) ≠ 0)
    (α : SL(3, K) →* G) (hker : α.ker ≤ Subgroup.center SL(3, K)) {U V : Subgroup G}
    (hU : U ≤ α.range) (hV : V ≤ α.range) (eU : SL(2, K) ≃* ↥U) (eV : SL(2, K) ≃* ↥V) {a b : G}
    (ha : a ∈ U) (hb : b ∈ V) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2)
    (haU : ∀ u ∈ U, u * a = a * u) (hbV : ∀ v ∈ V, v * b = b * v) (hab : a ≠ b)
    (hcomm : a * b = b * a) :
    α.range = U ⊔ V ∧ ∃ θ : SL(3, K) →* G, θ.ker ≤ Subgroup.center SL(3, K) ∧ θ.range = U ⊔ V := by
  obtain ⟨hstd, -⟩ := CFSG.GH74.GLS.LU.linearBlockStandardPair_of_central_involutions hK4 h2 α hker
    hU hV eU eV ha hb ha2 hb2 haU hbV hab hcomm
  obtain ⟨θ, hrange, hker', hB12, hB23⟩ := CFSG.ClassicalInvolution.WeakCT.pair_normalize hstd
  have hθ : θ.range = U ⊔ V := by
    rw [MonoidHom.range_eq_map, ← CFSG.ClassicalInvolution.WeakCT.B12_sup_B23 (K := K),
      Subgroup.map_sup, hB12, hB23]
  exact ⟨hrange.symm.trans hθ, θ, hker', hθ⟩

theorem unitary_pair_sup {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ f) (hF4 : 4 ≤ p ^ f) (α : CFSG.ClassicalInvolution.Phan.Su K p f 3 →* G)
    (hker : α.ker ≤ Subgroup.center (CFSG.ClassicalInvolution.Phan.Su K p f 3)) {U V : Subgroup G}
    (hU : U ≤ α.range) (hV : V ≤ α.range) (eU : SL(2, F) ≃* ↥U) (eV : SL(2, F) ≃* ↥V) {a b : G}
    (ha : a ∈ U) (hb : b ∈ V) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2)
    (haU : ∀ u ∈ U, u * a = a * u) (hbV : ∀ v ∈ V, v * b = b * v) (hab : a ≠ b)
    (hcomm : a * b = b * a) :
    α.range = U ⊔ V ∧ ∃ θ : CFSG.ClassicalInvolution.Phan.Su K p f 3 →* G,
      θ.ker ≤ Subgroup.center (CFSG.ClassicalInvolution.Phan.Su K p f 3) ∧ θ.range = U ⊔ V := by
  obtain ⟨hstd, -⟩ := CFSG.GH74.GLS.LU.unitaryBlockStandardPair_of_central_involutions hK hp hF hF4 α
    hker hU hV eU eV ha hb ha2 hb2 haU hbV hab hcomm
  obtain ⟨θ, hrange, hker', hB12, hB23⟩ := CFSG.ClassicalInvolution.Phan.pair_normalize hstd
  have hq : p ^ f ≠ 2 := by omega
  have hθ : θ.range = U ⊔ V := by
    rw [MonoidHom.range_eq_map, ← CFSG.ClassicalInvolution.Phan.B12_sup_B23_eq_top hK hq,
      Subgroup.map_sup, hB12, hB23]
  exact ⟨hrange.symm.trans hθ, θ, hker', hθ⟩

end Pairs


section Conj

variable {G : Type} [Group G]

theorem map_conj_centralizer (c : G) (S : Set G) :
    (centralizer S).map (MulAut.conj c).toMonoidHom = centralizer ((fun x => c * x * c⁻¹) '' S) := by
  have hf : ∀ y : G, (MulAut.conj c).toMonoidHom y = c * y * c⁻¹ := fun y => by simp
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    have h1 : s * y = y * s := mem_centralizer_iff.1 hy s hs
    rw [hf]
    calc c * s * c⁻¹ * (c * y * c⁻¹) = c * (s * y) * c⁻¹ := by group
      _ = c * (y * s) * c⁻¹ := by rw [h1]
      _ = c * y * c⁻¹ * (c * s * c⁻¹) := by group
  · intro hx
    refine ⟨c⁻¹ * x * c, ?_, by rw [hf]; group⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro s hs
    have h1 : c * s * c⁻¹ * x = x * (c * s * c⁻¹) := mem_centralizer_iff.1 hx _ ⟨s, hs, rfl⟩
    calc s * (c⁻¹ * x * c) = c⁻¹ * (c * s * c⁻¹ * x) * c := by group
      _ = c⁻¹ * (x * (c * s * c⁻¹)) * c := by rw [h1]
      _ = c⁻¹ * x * c * s := by group

theorem isComponent_map_conj {H J : Subgroup G} (h : IsComponent (J.subgroupOf H)) (c : G) :
    IsComponent ((J.map (MulAut.conj c).toMonoidHom).subgroupOf
      (H.map (MulAut.conj c).toMonoidHom)) := by
  have key : (J.map (MulAut.conj c).toMonoidHom).subgroupOf (H.map (MulAut.conj c).toMonoidHom) =
      (J.subgroupOf H).map ((MulAut.conj c).subgroupMap H).toMonoidHom := by
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨l, hl, hly⟩
      obtain ⟨k, hk, hky⟩ := y.2
      have hlk : l = k := (MulAut.conj c).injective (hly.trans hky.symm)
      subst hlk
      exact ⟨⟨l, hk⟩, hl, Subtype.ext (by simpa using hly)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by simp⟩
  rw [key]
  exact LocalCores.isComponent_map_mulEquiv ((MulAut.conj c).subgroupMap H) h

theorem IsSL2Comp.map_conj {F : Type*} [Field F] {w₁ e : G} {J : Subgroup G}
    (h : IsSL2Comp F w₁ e J) (c : G) :
    IsSL2Comp F (c * w₁ * c⁻¹) (c * e * c⁻¹) (J.map (MulAut.conj c).toMonoidHom) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hC : (centralizer ({w₁, e} : Set G)).map (MulAut.conj c).toMonoidHom =
      centralizer ({c * w₁ * c⁻¹, c * e * c⁻¹} : Set G) := by
    rw [map_conj_centralizer, Set.image_pair]
  refine ⟨?_, ?_, ⟨e, h3, by simp⟩, ?_⟩
  · rw [← hC]
    exact Subgroup.map_mono h1
  · rw [← hC]
    exact isComponent_map_conj h2 c
  · obtain ⟨φ⟩ := h4
    exact ⟨φ.trans (J.equivMapOfInjective _ (MulAut.conj c).injective)⟩

end Conj

theorem b_S3_J_contain_of_in_Iw (hJ : B_S3_J_in_Iw) : B_S3_J_contain := by
  intro G _ _ hG t p f v w Iv Iw Ivw P V v₁ hconf F _ _ hF J₀ J₁ J₂ h₀ h₁ h₂
  have hJ' := hJ G hG t p f v w Iv Iw Ivw P V v₁ hconf F inferInstance inferInstance hF
  refine ⟨hJ' v hconf.hv J₀ h₀, hJ' v₁ hconf.hv₁ J₁ h₁, ?_⟩
  have hx : w * v₁ ∈ Wset V w := by
    show w * (w * v₁) ∈ V
    rw [← mul_assoc, hconf.setup.w_sq, one_mul]
    exact hconf.hv₁.1
  obtain ⟨n, hn, hn', hnw⟩ := hconf.conj (w * v₁) hx
  have hw : n⁻¹ * (w * v₁) * n⁻¹⁻¹ = w := by
    rw [← hnw]
    group
  have hback : ∀ (K : Subgroup G), K.map (MulAut.conj n⁻¹).toMonoidHom ≤ Iw →
      K ≤ Iw.map (MulAut.conj n).toMonoidHom := by
    intro K hK x hx
    exact ⟨n⁻¹ * x * n⁻¹⁻¹, hK ⟨x, hx, by simp⟩, by
      show n * (n⁻¹ * x * n⁻¹⁻¹) * n⁻¹ = x
      group⟩
  have hmem : ∀ a ∈ Vsharp V, n⁻¹ * a * n⁻¹⁻¹ ∈ Vsharp V := by
    intro a ha
    refine ⟨hn' a ha.1, fun h1 => ha.2 ?_⟩
    calc a = n * (n⁻¹ * a * n⁻¹⁻¹) * n⁻¹ := by group
      _ = 1 := by rw [h1]; group
  refine ⟨n, hback J₁ ?_, hback J₂ ?_⟩
  · have h1' := h₁.mul.map_conj n⁻¹
    rw [hw] at h1'
    exact hJ' _ (hmem v₁ hconf.hv₁) _ h1'
  · have h2' := h₂.map_conj n⁻¹
    rw [hw] at h2'
    exact hJ' _ (hmem v hconf.hv) _ h2'

theorem b_S3_sl3pair_lin_of_cover (hcov : B_L3_cover) (hcont : B_S3_J_contain) :
    B_S3_sl3pair_lin := by
  intro G _ _ hG p f v w Iv Iw Ivw P V v₁ hconf F _ _ hF J₀ J₁ J₂ h₀ h₁ h₂
  obtain ⟨hJ₀, hJ₁, g, hJ₁g, hJ₂g⟩ := hcont G hG .PSL p f v w Iv Iw Ivw P V v₁ hconf F
    inferInstance inferInstance hF J₀ J₁ J₂ h₀ h₁ h₂
  have C := hconf.conf
  have h2 : (2 : F) ≠ 0 :=
    Ring.two_ne_zero (ringChar_ne_two_of_card_pow C.prime.1 C.prime.2.1 hF)
  have hK4 : 4 ≤ Nat.card F := by
    rw [hF]
    have := C.prime.2.2
    omega
  obtain ⟨α, hker, hrange⟩ := (hcov G p f C.prime.1 C.prime.2.1 C.prime.2.2 Iw
    C.comp_w.1.isQuasisimple C.odd_w).1 C.model_w F inferInstance inferInstance hF
  have hv2 : v * v = 1 := hconf.setup.V_sq v hconf.hv.1
  have hv₁2 : v₁ * v₁ = 1 := hconf.setup.V_sq v₁ hconf.hv₁.1
  have hvo : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hv2) hconf.hv.2
  have hv₁o : orderOf v₁ = 2 := orderOf_eq_prime (by rw [sq]; exact hv₁2) hconf.hv₁.2
  have hcomm : v * v₁ = v₁ * v := hconf.setup.V_comm v hconf.hv.1 v₁ hconf.hv₁.1
  obtain ⟨hr1, θ₁, hθ₁, hθ₁r⟩ := linear_pair_sup hK4 h2 α hker (U := J₀) (V := J₁)
    (by rw [hrange]; exact hJ₀) (by rw [hrange]; exact hJ₁) (Classical.choice h₀.iso)
    (Classical.choice h₁.iso) h₀.mem h₁.mem hvo hv₁o (fun u hu => (h₀.commute u hu).2)
    (fun u hu => (h₁.commute u hu).2) hconf.hne hcomm
  obtain ⟨α', hker', hrange'⟩ := exists_hom_conj α hker g
  obtain ⟨-, θ₂, hθ₂, hθ₂r⟩ := linear_pair_sup hK4 h2 α' hker' (U := J₁) (V := J₂)
    (by rw [hrange', hrange]; exact hJ₁g) (by rw [hrange', hrange]; exact hJ₂g)
    (Classical.choice h₁.iso) (Classical.choice h₂.iso) h₁.mem h₂.mem hv₁o hvo
    (fun u hu => (h₁.commute u hu).2) (fun u hu => (h₂.commute u hu).2) hconf.hne.symm hcomm.symm
  exact ⟨hr1.symm.trans hrange, ⟨θ₁, hθ₁, hθ₁r⟩, ⟨θ₂, hθ₂, hθ₂r⟩⟩

theorem b_S3_sl3pair_uni_of_cover (hcov : B_L3_cover) (hcont : B_S3_J_contain) :
    B_S3_sl3pair_uni := by
  intro G _ _ hG p f v w Iv Iw Ivw P V v₁ hconf F _ _ hF J₀ J₁ J₂ h₀ h₁ h₂
  obtain ⟨hJ₀, hJ₁, g, hJ₁g, hJ₂g⟩ := hcont G hG .PSU p f v w Iv Iw Ivw P V v₁ hconf F
    inferInstance inferInstance hF J₀ J₁ J₂ h₀ h₁ h₂
  have C := hconf.conf
  have : Fact p.Prime := ⟨C.prime.1⟩
  have hf : f ≠ 0 := by
    rintro rfl
    have := C.prime.2.2
    rw [pow_zero] at this
    omega
  have hF4 : 4 ≤ p ^ f := by
    have := C.prime.2.2
    omega
  have hF₂ : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), mul_comm, pow_mul]
  obtain ⟨α₀, hker₀, hrange₀⟩ := (hcov G p f C.prime.1 C.prime.2.1 C.prime.2.2 Iw
    C.comp_w.1.isQuasisimple C.odd_w).2 C.model_w (GaloisField p (2 * f)) inferInstance inferInstance
    hF₂
  let e : CFSG.ClassicalInvolution.Phan.Su (GaloisField p (2 * f)) p f 3 ≃*
      ↥(StatedSU 3 (p ^ f) (GaloisField p (2 * f))) :=
    MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF₂ 3)
  obtain ⟨α, hker, hrange⟩ := exists_hom_of_mulEquiv e.symm α₀ hker₀
  have hrangeI : α.range = Iw := hrange.trans hrange₀
  have hv2 : v * v = 1 := hconf.setup.V_sq v hconf.hv.1
  have hv₁2 : v₁ * v₁ = 1 := hconf.setup.V_sq v₁ hconf.hv₁.1
  have hvo : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hv2) hconf.hv.2
  have hv₁o : orderOf v₁ = 2 := orderOf_eq_prime (by rw [sq]; exact hv₁2) hconf.hv₁.2
  have hcomm : v * v₁ = v₁ * v := hconf.setup.V_comm v hconf.hv.1 v₁ hconf.hv₁.1
  obtain ⟨hr1, θ₁, hθ₁, hθ₁r⟩ := unitary_pair_sup hF₂ C.prime.2.1 hF hF4 α hker (U := J₀) (V := J₁)
    (by rw [hrangeI]; exact hJ₀) (by rw [hrangeI]; exact hJ₁) (Classical.choice h₀.iso)
    (Classical.choice h₁.iso) h₀.mem h₁.mem hvo hv₁o (fun u hu => (h₀.commute u hu).2)
    (fun u hu => (h₁.commute u hu).2) hconf.hne hcomm
  obtain ⟨α', hker', hrange'⟩ := exists_hom_conj α hker g
  obtain ⟨-, θ₂, hθ₂, hθ₂r⟩ := unitary_pair_sup hF₂ C.prime.2.1 hF hF4 α' hker' (U := J₁) (V := J₂)
    (by rw [hrange', hrangeI]; exact hJ₁g) (by rw [hrange', hrangeI]; exact hJ₂g)
    (Classical.choice h₁.iso) (Classical.choice h₂.iso) h₁.mem h₂.mem hv₁o hvo
    (fun u hu => (h₁.commute u hu).2) (fun u hu => (h₂.commute u hu).2) hconf.hne.symm hcomm.symm
  refine ⟨hr1.symm.trans hrangeI, GaloisField p (2 * f), inferInstance, inferInstance, hF₂, ?_, ?_⟩
  · obtain ⟨θ', hθ', hθ'r⟩ := exists_hom_of_mulEquiv e θ₁ hθ₁
    exact ⟨θ', hθ', hθ'r.trans hθ₁r⟩
  · obtain ⟨θ', hθ', hθ'r⟩ := exists_hom_of_mulEquiv e θ₂ hθ₂
    exact ⟨θ', hθ', hθ'r.trans hθ₂r⟩

end CFSG.GH74.Generic.S3
