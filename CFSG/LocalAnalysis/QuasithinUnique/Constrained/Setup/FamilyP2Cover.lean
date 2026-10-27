module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2General
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBinary
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG CFSG.GorensteinWalter CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X3 CFSG.Quasithin

theorem mem_sup_of_le_normalizer {G : Type*} [Group G] {L A : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (L : Set G)) {z : G} (hz : z ∈ L ⊔ A) :
    ∃ l ∈ L, ∃ a ∈ A, z = l * a := by
  let S : Subgroup G :=
    { carrier := {x | ∃ l ∈ L, ∃ a ∈ A, x = l * a}
      one_mem' := ⟨1, L.one_mem, 1, A.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨l₁, hl₁, a₁, ha₁, rfl⟩ ⟨l₂, hl₂, a₂, ha₂, rfl⟩
        have hn : a₁ * l₂ * a₁⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hA ha₁) l₂).1 hl₂
        refine ⟨l₁ * (a₁ * l₂ * a₁⁻¹), L.mul_mem hl₁ hn, a₁ * a₂, A.mul_mem ha₁ ha₂, ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨l, hl, a, ha, rfl⟩
        have hn : a⁻¹ * l⁻¹ * a ∈ L := by
          have := (Subgroup.mem_normalizer_iff.1 (hA (A.inv_mem ha)) l⁻¹).1 (L.inv_mem hl)
          simpa using this
        refine ⟨a⁻¹ * l⁻¹ * a, hn, a⁻¹, A.inv_mem ha, ?_⟩
        group }
  have hle : L ⊔ A ≤ S := sup_le (fun l hl => ⟨l, hl, 1, A.one_mem, (mul_one l).symm⟩)
    (fun a ha => ⟨1, L.one_mem, a, ha, (one_mul a).symm⟩)
  exact hle hz

section AutStructure

variable {p : ℕ} [hpf : Fact p.Prime]

theorem isOddPrimePower_card_zmod (hp5 : 5 ≤ p) : IsOddPrimePower (Nat.card (ZMod p)) :=
  isOddPrimePower_prime hpf.out (by omega)

omit hpf in
theorem three_lt_card_zmod (hp5 : 5 ≤ p) : 3 < Nat.card (ZMod p) := by
  rw [Nat.card_zmod]
  omega

theorem pgl2InnerAutPSL2_surjective_zmod (hp5 : 5 ≤ p) :
    Function.Surjective (pgl2InnerAutPSL2 (ZMod p) (isOddPrimePower_card_zmod hp5)
      (three_lt_card_zmod hp5)) := by
  intro α
  obtain ⟨x, hx⟩ := pGammaL2ToMulAutPSL2_surjective (ZMod p) (p := p) (f := 1)
    (by rw [Nat.card_zmod, pow_one]) (isOddPrimePower_card_zmod hp5) (three_lt_card_zmod hp5) α
  have hσ : x.right = 1 := Subsingleton.elim _ _
  refine ⟨x.left, ?_⟩
  have hx' : x = SemidirectProduct.inl x.left * SemidirectProduct.inr x.right :=
    (SemidirectProduct.inl_left_mul_inr_right x).symm
  rw [hx', map_mul, pGammaL2ToMulAutPSL2_inl, pGammaL2ToMulAutPSL2_inr, hσ, map_one,
    mul_one] at hx
  exact hx

@[expose] noncomputable def autPSL2EquivPGL2 (hp5 : 5 ≤ p) :
    PGL2 (ZMod p) ≃* MulAut (PSL2 (ZMod p)) :=
  MulEquiv.ofBijective (pgl2InnerAutPSL2 (ZMod p) (isOddPrimePower_card_zmod hp5)
    (three_lt_card_zmod hp5))
    ⟨pgl2InnerAutPSL2_injective _ _ _, pgl2InnerAutPSL2_surjective_zmod hp5⟩

theorem autPSL2EquivPGL2_toPGL (hp5 : 5 ≤ p) (y : PSL2 (ZMod p)) :
    autPSL2EquivPGL2 hp5 (Matrix.ProjectiveSpecialLinearGroup.toPGL y) = MulAut.conj y :=
  pgl2InnerAutPSL2_toPGL (ZMod p) _ _ y

theorem aut_structure (hp5 : 5 ≤ p) {Hg : Type*} [Group Hg] {N : Subgroup Hg} [N.Normal]
    (θ : N ≃* PSL2 (ZMod p)) (hC : ∀ z : Hg, (∀ n ∈ N, z * n = n * z) → z = 1) :
    ∃ (Y : Subgroup (PGL2 (ZMod p))) (e : Hg ≃* Y), (Y = pglS (ZMod p) ∨ Y = ⊤) ∧
      ∀ n : N, ((e (n : Hg) : Y) : PGL2 (ZMod p)) =
        Matrix.ProjectiveSpecialLinearGroup.toPGL (θ n) := by
  let Φ : Hg →* PGL2 (ZMod p) := (autPSL2EquivPGL2 hp5).symm.toMonoidHom.comp
    ((MulAut.congr θ).toMonoidHom.comp MulAut.conjNormal)
  have hΦ : ∀ h : Hg, autPSL2EquivPGL2 hp5 (Φ h) = (MulAut.congr θ) (MulAut.conjNormal h) :=
    fun h => MulEquiv.apply_symm_apply _ _
  have hΦn : ∀ n : N, Φ (n : Hg) = Matrix.ProjectiveSpecialLinearGroup.toPGL (θ n) := by
    intro n
    apply (autPSL2EquivPGL2 hp5).injective
    rw [hΦ, autPSL2EquivPGL2_toPGL]
    ext x
    show θ ((MulAut.conjNormal (n : Hg)) (θ.symm x)) = (MulAut.conj (θ n)) x
    have h1 : (MulAut.conjNormal (n : Hg)) (θ.symm x) = n * θ.symm x * n⁻¹ := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      rfl
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulAut.conj_apply]
  have hinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro h hh
    rw [MonoidHom.mem_ker] at hh
    rw [Subgroup.mem_bot]
    apply hC
    intro n hn
    have h1 : (MulAut.congr θ) (MulAut.conjNormal h) = 1 := by
      rw [← hΦ, hh, map_one]
    have h2 : MulAut.conjNormal h = (1 : MulAut N) :=
      (MulAut.congr θ).injective (by rw [h1, map_one])
    have h3 := congrArg (fun f : MulAut N => ((f ⟨n, hn⟩ : N) : Hg)) h2
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
    exact mul_inv_eq_iff_eq_mul.1 h3
  let Y : Subgroup (PGL2 (ZMod p)) := Φ.range
  let e : Hg ≃* Y := MonoidHom.ofInjective hinj
  have he : ∀ x : Hg, ((e x : Y) : PGL2 (ZMod p)) = Φ x := fun x => rfl
  have hS : pglS (ZMod p) ≤ Y := by
    rintro _ ⟨y, rfl⟩
    exact ⟨(θ.symm y : N), by rw [hΦn, MulEquiv.apply_symm_apply]⟩
  have hK : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have hidx : (pglS (ZMod p)).index = 2 := pglS_index hK
  have hdvd : Y.index ∣ 2 := by
    have h0 := Subgroup.index_dvd_of_le hS
    rwa [hidx] at h0
  have hY : Y = pglS (ZMod p) ∨ Y = ⊤ := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact Or.inr (Subgroup.index_eq_one.1 h1)
    · left
      have h3 := Subgroup.relIndex_mul_index hS
      rw [h2, hidx] at h3
      have h4 : (pglS (ZMod p)).relIndex Y = 1 := by omega
      exact le_antisymm (Subgroup.relIndex_eq_one.1 h4) hS
  exact ⟨Y, e, hY, fun n => by rw [he, hΦn]⟩

end AutStructure

section Transport

variable {Hg G' E : Type*} [Group Hg] [Group G'] [AddCommGroup E] [Module (ZMod 2) E]

theorem commSub_mono (ρ : Hg →* (E ≃ₗ[ZMod 2] E)) {A A' : Subgroup Hg} (h : A ≤ A') :
    commSub ρ A ≤ commSub ρ A' :=
  Submodule.span_mono fun _ ⟨a, ha, e, hx⟩ => ⟨a, h ha, e, hx⟩

theorem fixedSub_comp_equiv (e' : Hg ≃* G') (ρH : Hg →* (E ≃ₗ[ZMod 2] E)) (M : Subgroup Hg) :
    fixedSub (ρH.comp e'.symm.toMonoidHom) (M.map e'.toMonoidHom) = fixedSub ρH M := by
  ext x
  rw [mem_fixedSub, mem_fixedSub]
  constructor
  · intro h a ha
    have := h (e' a) (Subgroup.mem_map.2 ⟨a, ha, rfl⟩)
    simpa using this
  · rintro h _ ⟨a, ha, rfl⟩
    simpa using h a ha

theorem commSub_comp_equiv (e' : Hg ≃* G') (ρH : Hg →* (E ≃ₗ[ZMod 2] E)) (M : Subgroup Hg) :
    commSub (ρH.comp e'.symm.toMonoidHom) (M.map e'.toMonoidHom) = commSub ρH M := by
  unfold commSub
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, e, rfl⟩
    exact ⟨a, ha, e, by simp⟩
  · rintro ⟨a, ha, e, rfl⟩
    exact ⟨e' a, Subgroup.mem_map.2 ⟨a, ha, rfl⟩, e, by simp⟩

theorem natCard_map_equiv (e' : Hg ≃* G') (M : Subgroup Hg) :
    Nat.card (M.map e'.toMonoidHom) = Nat.card M :=
  (Nat.card_congr (e'.subgroupMap M).toEquiv).symm

theorem transport_offender [Module.Finite (ZMod 2) E] (e' : Hg ≃* G')
    (ρH : Hg →* (E ≃ₗ[ZMod 2] E)) {B : Subgroup Hg} (hB1 : B ≠ ⊥)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ a ∈ B, a * a = 1)
    (hoff : Module.finrank (ZMod 2) E - Module.finrank (ZMod 2) (fixedSub ρH B) ≤
      Nat.log 2 (Nat.card B)) :
    B.map e'.toMonoidHom ≠ ⊥ ∧ (∀ a ∈ B.map e'.toMonoidHom, ∀ b ∈ B.map e'.toMonoidHom,
      a * b = b * a) ∧ (∀ a ∈ B.map e'.toMonoidHom, a * a = 1) ∧
      Module.finrank (ZMod 2) E - Module.finrank (ZMod 2)
        (fixedSub (ρH.comp e'.symm.toMonoidHom) (B.map e'.toMonoidHom)) ≤
        Nat.log 2 (Nat.card (B.map e'.toMonoidHom)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _
      (show Function.Injective e'.toMonoidHom from e'.injective)]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show e' a * e' b = e' b * e' a
    rw [← map_mul, ← map_mul, hBc a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    show e' a * e' a = 1
    rw [← map_mul, hB2 a ha, map_one]
  · rwa [fixedSub_comp_equiv, natCard_map_equiv]

end Transport

section ModuleData

variable {p : ℕ} [hpf : Fact p.Prime]

theorem prime_le_seven_of_module_data
    (hp5 : 5 ≤ p) {E : Type*} [AddCommGroup E]
    [Module (ZMod 2) E] [Module.Finite (ZMod 2) E] [Nontrivial E] {Hg : Type*} [Group Hg]
    (ρH : Hg →* (E ≃ₗ[ZMod 2] E)) {N : Subgroup Hg} {Y : Subgroup (PGL2 (ZMod p))}
    (e : Hg ≃* Y) (hY : Y = pglS (ZMod p) ∨ Y = ⊤)
    (hN : ∀ n ∈ N, ((e n : Y) : PGL2 (ZMod p)) ∈ pglS (ZMod p)) (hcomm : commSub ρH N = ⊤)
    {B : Subgroup Hg} (hB1 : B ≠ ⊥) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hB2 : ∀ a ∈ B, a * a = 1)
    (hoff : Module.finrank (ZMod 2) E - Module.finrank (ZMod 2) (fixedSub ρH B) ≤
      Nat.log 2 (Nat.card B)) : p = 5 ∨ p = 7 := by
  rcases hY with hY | hY
  · have hrange : (p2ToPGL p).range = pglS (ZMod p) := by
      ext x
      rw [MonoidHom.mem_range]
      exact mem_pglS_iff.symm
    let e' : Hg ≃* projectiveSL 2 (ZMod p) :=
      e.trans ((MulEquiv.subgroupCongr (hY.trans hrange.symm)).trans
        (MonoidHom.ofInjective (p2ToPGL_injective (p := p))).symm)
    obtain ⟨hB1', hBc', hB2', hoff'⟩ := transport_offender e' ρH hB1 hBc hB2 hoff
    have hE : commSub (ρH.comp e'.symm.toMonoidHom) ⊤ = ⊤ := by
      rw [eq_top_iff, ← hcomm, ← commSub_comp_equiv e' ρH N]
      exact commSub_mono _ le_top
    exact (p2_internal_offender_actor hp5 (ρH.comp e'.symm.toMonoidHom) hE hB1' hBc' hB2'
      hoff').2.2
  · let e' : Hg ≃* PGL2 (ZMod p) := e.trans ((MulEquiv.subgroupCongr hY).trans Subgroup.topEquiv)
    obtain ⟨hB1', hBc', hB2', hoff'⟩ := transport_offender e' ρH hB1 hBc hB2 hoff
    have hE : commSub (ρH.comp e'.symm.toMonoidHom) (pglS (ZMod p)) = ⊤ := by
      rw [eq_top_iff, ← hcomm, ← commSub_comp_equiv e' ρH N]
      refine commSub_mono _ ?_
      rintro _ ⟨n, hn, rfl⟩
      exact hN n hn
    exact (pgl2_general_offender_actor hp5 (ρH.comp e'.symm.toMonoidHom) hE hB1' hBc' hB2'
      hoff').2.2

end ModuleData

theorem finrank_sub_le_log_of_card_le {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    (F : Submodule (ZMod 2) E) {n k : ℕ} (hn : n = 2 ^ k) (h : Nat.card E ≤ n * Nat.card F) :
    Module.finrank (ZMod 2) E - Module.finrank (ZMod 2) F ≤ Nat.log 2 n := by
  have hE : Nat.card E = 2 ^ Module.finrank (ZMod 2) E := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hF : Nat.card F = 2 ^ Module.finrank (ZMod 2) F := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hE, hF, hn, ← pow_add] at h
  have h2 : Module.finrank (ZMod 2) E ≤ k + Module.finrank (ZMod 2) F :=
    (Nat.pow_le_pow_iff_right (by norm_num)).1 h
  rw [hn, Nat.log_pow (by norm_num)]
  omega

theorem irr_module_of_irr {W : Type} [CommGroup W] [Fact (∀ w : W, w * w = 1)]
    {L : Subgroup (MulAut W)}
    (hL : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (D : Submodule (ZMod 2) (Additive W)) (hD : ∀ g ∈ L, ∀ x ∈ D, binaryLin g x ∈ D) :
    D = ⊥ ∨ D = ⊤ := by
  let U : Subgroup W :=
    { carrier := {w | Additive.ofMul w ∈ D}
      one_mem' := D.zero_mem
      mul_mem' := fun {a b} ha hb => D.add_mem ha hb
      inv_mem' := fun {a} ha => D.neg_mem ha }
  have hU : ∀ g ∈ L, ∀ u ∈ U, g u ∈ U := fun g hg u hu => hD g hg _ hu
  rcases hL U hU with h | h
  · left
    refine eq_bot_iff.2 fun x hx => ?_
    have hx' : Additive.toMul x ∈ U := by
      show Additive.ofMul (Additive.toMul x) ∈ D
      exact hx
    rw [h, Subgroup.mem_bot] at hx'
    rw [Submodule.mem_bot]
    exact Additive.toMul.injective hx'
  · right
    refine eq_top_iff.2 fun x _ => ?_
    have hx' : Additive.toMul x ∈ U := by rw [h]; trivial
    exact hx'

section Main

variable {p : ℕ} [hpf : Fact p.Prime]

theorem primeLinearTwoCover
    (hp11 : 11 ≤ p) {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) [Nontrivial W] {L : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L)
    (hL : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (α : CQ L ≃* projectiveSL 2 (ZMod p)) :
    Subgroup.center ↥L = ⊥ ∧ ∀ A : Subgroup (MulAut W),
      A ≤ Subgroup.normalizer (L : Set (MulAut W)) → A ≠ ⊥ → IsElemAbelian2 A →
        Nat.card A * Nat.card (fixV A) < Nat.card W := by
  have hp5 : 5 ≤ p := by omega
  have : Fact (∀ w : W, w * w = 1) := ⟨hW⟩
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have := hperf
  have hodd := odd_card_center_of_irreducible hW hL
  let π : ↥L →* projectiveSL 2 (ZMod p) :=
    α.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπs : Function.Surjective π := α.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπk : π.ker = Subgroup.center ↥L := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : (QuotientGroup.mk x : CQ L) = 1 := α.injective (by rw [map_one]; exact h)
      exact (QuotientGroup.eq_one_iff x).1 h1
    · intro h
      have h1 : (QuotientGroup.mk x : CQ L) = 1 := (QuotientGroup.eq_one_iff x).2 h
      show α (QuotientGroup.mk x) = 1
      rw [h1, map_one]
  have hbound : Nat.card π.ker ≤ 2 := p2_central_kernel_bound hp5 π hπs hπk.le
  have hcenter : Subgroup.center ↥L = ⊥ := by
    rw [hπk] at hbound
    have h1 : Nat.card (Subgroup.center ↥L) = 1 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    exact Subgroup.card_eq_one.1 h1
  refine ⟨hcenter, fun A hA hA1 hA2 => ?_⟩
  by_contra hne
  push Not at hne
  have hπinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 (hπk.trans hcenter)
  let θ : ↥L ≃* PSL2 (ZMod p) := (MulEquiv.ofBijective π ⟨hπinj, hπs⟩).trans (p2Equiv (ZMod p))
  have hHn : L ⊔ A ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    sup_le Subgroup.le_normalizer hA
  have hNnormal : (L.subgroupOf (L ⊔ A)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hHn
  let θ' : (L.subgroupOf (L ⊔ A)) ≃* PSL2 (ZMod p) :=
    (Subgroup.subgroupOfEquivOfLe (le_sup_left : L ≤ L ⊔ A)).trans θ
  have hC : ∀ z : ↥(L ⊔ A), (∀ n ∈ L.subgroupOf (L ⊔ A), z * n = n * z) → z = 1 := by
    intro z hz
    obtain ⟨l, hl, a, ha, hzla⟩ := mem_sup_of_le_normalizer hA z.2
    have hzc : ∀ y ∈ L, (z : MulAut W) * y = y * (z : MulAut W) := by
      intro y hy
      have hyN : (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(L ⊔ A)) ∈ L.subgroupOf (L ⊔ A) := hy
      exact congrArg Subtype.val (hz _ hyN)
    have ha2 : a * a = 1 := by
      have := hA2.2 a ha
      rwa [pow_two] at this
    have hzl : (z : MulAut W) * l⁻¹ = l⁻¹ * (z : MulAut W) := hzc _ (L.inv_mem hl)
    have hal : a = l⁻¹ * (z : MulAut W) := by rw [hzla]; group
    have hkey : (l⁻¹ * (z : MulAut W)) * (l⁻¹ * (z : MulAut W)) =
        l⁻¹ * l⁻¹ * ((z : MulAut W) * (z : MulAut W)) := by
      calc (l⁻¹ * (z : MulAut W)) * (l⁻¹ * (z : MulAut W))
          = l⁻¹ * ((z : MulAut W) * l⁻¹) * (z : MulAut W) := by group
        _ = l⁻¹ * (l⁻¹ * (z : MulAut W)) * (z : MulAut W) := by rw [hzl]
        _ = l⁻¹ * l⁻¹ * ((z : MulAut W) * (z : MulAut W)) := by group
    have hzz : (z : MulAut W) * (z : MulAut W) = l * l := by
      rw [← hal, ha2] at hkey
      have := eq_inv_of_mul_eq_one_right hkey.symm
      simpa using this
    have hzzL : (z : MulAut W) * (z : MulAut W) ∈ L := by rw [hzz]; exact L.mul_mem hl hl
    have hzz1 : (z : MulAut W) * (z : MulAut W) = 1 := by
      have hcen : (⟨(z : MulAut W) * (z : MulAut W), hzzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        show (y : MulAut W) * ((z : MulAut W) * (z : MulAut W)) =
          ((z : MulAut W) * (z : MulAut W)) * (y : MulAut W)
        have hy := hzc y y.2
        calc (y : MulAut W) * ((z : MulAut W) * (z : MulAut W))
            = ((y : MulAut W) * (z : MulAut W)) * (z : MulAut W) := by rw [mul_assoc]
          _ = ((z : MulAut W) * (y : MulAut W)) * (z : MulAut W) := by rw [← hy]
          _ = (z : MulAut W) * ((y : MulAut W) * (z : MulAut W)) := by rw [mul_assoc]
          _ = (z : MulAut W) * ((z : MulAut W) * (y : MulAut W)) := by rw [← hy]
          _ = ((z : MulAut W) * (z : MulAut W)) * (y : MulAut W) := by rw [mul_assoc]
      rw [hcenter, Subgroup.mem_bot] at hcen
      exact congrArg Subtype.val hcen
    have hz1 : (z : MulAut W) = 1 :=
      eq_one_of_centralizes_irreducible hW hL (fun l hl => (hzc l hl)) hzz1
    exact Subtype.ext hz1
  obtain ⟨Y, e, hY, he⟩ := aut_structure hp5 θ' hC
  have hAH : A ≤ L ⊔ A := le_sup_right
  let ρH : ↥(L ⊔ A) →* (Additive W ≃ₗ[ZMod 2] Additive W) := binaryLin.comp (L ⊔ A).subtype
  have hN : ∀ n ∈ L.subgroupOf (L ⊔ A), ((e n : Y) : PGL2 (ZMod p)) ∈ pglS (ZMod p) := by
    intro n hn
    have := he ⟨n, hn⟩
    rw [show (((⟨n, hn⟩ : L.subgroupOf (L ⊔ A)) : ↥(L ⊔ A))) = n from rfl] at this
    rw [this]
    exact ⟨_, rfl⟩
  have hρH : ∀ (g : ↥(L ⊔ A)) (v : Additive W), ρH g v = Additive.ofMul ((g : MulAut W)
      (Additive.toMul v)) := fun g v => rfl
  have hcomm : commSub ρH (L.subgroupOf (L ⊔ A)) = ⊤ := by
    set D := commSub ρH (L.subgroupOf (L ⊔ A)) with hD
    have hDinv : ∀ g ∈ L, ∀ x ∈ D, binaryLin g x ∈ D := by
      intro g hg x hx
      have hgH : g ∈ L ⊔ A := Subgroup.mem_sup_left hg
      have hle : D ≤ D.comap (binaryLin g : Additive W →ₗ[ZMod 2] Additive W) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨n, hn, v, rfl⟩
        have hn' : (⟨g, hgH⟩ * n * ⟨g, hgH⟩⁻¹ : ↥(L ⊔ A)) ∈ L.subgroupOf (L ⊔ A) := by
          have hnL : (n : MulAut W) ∈ L := hn
          show g * (n : MulAut W) * g⁻¹ ∈ L
          exact L.mul_mem (L.mul_mem hg hnL) (L.inv_mem hg)
        have hgg : ∀ u : Additive W, binaryLin g⁻¹ (binaryLin g u) = u := fun u => by
          rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
          rfl
        have hkey : binaryLin g (ρH n v - v) =
            ρH (⟨g, hgH⟩ * n * ⟨g, hgH⟩⁻¹) (binaryLin g v) - binaryLin g v := by
          rw [map_sub]
          congr 1
          show binaryLin g (binaryLin (n : MulAut W) v) =
            binaryLin (g * (n : MulAut W) * g⁻¹) (binaryLin g v)
          rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgg]
        show binaryLin g (ρH n v - v) ∈ D
        rw [hkey]
        exact Submodule.subset_span ⟨_, hn', binaryLin g v, rfl⟩
      exact hle hx
    rcases irr_module_of_irr hL D hDinv with h | h
    · exfalso
      have hLne : ∃ l ∈ L, l ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have hsub : Subsingleton ↥L := ⟨fun x y => Subtype.ext
          ((hcon x x.2).trans (hcon y y.2).symm)⟩
        have : Subsingleton (CQ L) := inferInstance
        have hnt := (p2_isSimpleGroup (p := p) hp5).toNontrivial
        have : Subsingleton (projectiveSL 2 (ZMod p)) := α.symm.injective.subsingleton
        exact not_subsingleton _ this
      obtain ⟨l, hl, hl1⟩ := hLne
      obtain ⟨w, hw⟩ : ∃ w : W, l w ≠ w := by
        by_contra hcon
        push Not at hcon
        exact hl1 (MulEquiv.ext hcon)
      have hlN : (⟨l, Subgroup.mem_sup_left hl⟩ : ↥(L ⊔ A)) ∈ L.subgroupOf (L ⊔ A) := hl
      have hmem : ρH ⟨l, Subgroup.mem_sup_left hl⟩ (Additive.ofMul w) - Additive.ofMul w ∈ D :=
        Submodule.subset_span ⟨_, hlN, Additive.ofMul w, rfl⟩
      rw [h, Submodule.mem_bot] at hmem
      apply hw
      have h1 := congrArg Additive.toMul hmem
      simp only [hρH, toMul_sub, toMul_ofMul, toMul_zero] at h1
      exact div_eq_one.1 h1
    · exact h
  have hB1 : A.subgroupOf (L ⊔ A) ≠ ⊥ := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA1
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨⟨a, hAH a.2⟩, a.2⟩, fun h => ha ?_⟩
    exact Subtype.ext (congrArg (fun x : ↥(A.subgroupOf (L ⊔ A)) => ((x : ↥(L ⊔ A)) : MulAut W)) h)
  have hBc : ∀ a ∈ A.subgroupOf (L ⊔ A), ∀ b ∈ A.subgroupOf (L ⊔ A), a * b = b * a :=
    fun a ha b hb => Subtype.ext (hA2.1 _ ha _ hb)
  have hB2 : ∀ a ∈ A.subgroupOf (L ⊔ A), a * a = 1 := fun a ha => by
    apply Subtype.ext
    have := hA2.2 _ ha
    rwa [pow_two] at this
  have hfix : Nat.card (fixedSub ρH (A.subgroupOf (L ⊔ A))) = Nat.card (fixV A) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨Additive.toMul x.1, fun a ha => ?_⟩
        invFun := fun w => ⟨Additive.ofMul w.1, fun b hb => ?_⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun w => Subtype.ext rfl }
    · have h1 := x.2 ⟨a, hAH ha⟩ ha
      exact congrArg Additive.toMul h1
    · have hb' : (b : MulAut W) ∈ A := hb
      have h1 := w.2 (b : MulAut W) hb'
      exact congrArg Additive.ofMul h1
  have hcardB : Nat.card (A.subgroupOf (L ⊔ A)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
  have hpgrp : IsPGroup 2 (A.subgroupOf (L ⊔ A)) := fun a => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (hB2 (a : ↥(L ⊔ A)) a.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hpgrp
  have hcardE : Nat.card (Additive W) = Nat.card W := Nat.card_congr Additive.toMul
  have hoff : Module.finrank (ZMod 2) (Additive W) -
      Module.finrank (ZMod 2) (fixedSub ρH (A.subgroupOf (L ⊔ A))) ≤
        Nat.log 2 (Nat.card (A.subgroupOf (L ⊔ A))) := by
    refine finrank_sub_le_log_of_card_le _ hk ?_
    rw [hcardE, hcardB, hfix]
    exact hne
  have hp57 := prime_le_seven_of_module_data hp5 ρH e hY hN hcomm hB1 hBc hB2 hoff
  omega

end Main

end CFSG.QuasithinUnique.Setup.Family
