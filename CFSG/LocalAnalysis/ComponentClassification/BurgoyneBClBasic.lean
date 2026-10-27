module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieL1
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOuter

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Cl

open CFSG Subgroup CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.CatLeafProof.EndOddLin
open scoped MatrixGroups commutatorElement

@[expose] def NoL2At {S : Type} [Group S] (v : MulAut S) : Prop :=
  ∀ R : Subgroup S, R ≤ autFixed v → IsPComponent 2 (R.subgroupOf (autFixed v)) →
    ∀ (p₁ n₁ : ℕ) [Fact p₁.Prime], p₁ ≠ 2 → 0 < n₁ →
    ∀ (M : Subgroup R) [M.Normal], Odd (Nat.card M) →
      Nonempty (R ⧸ M ≃* PSL(2, GaloisField p₁ n₁)) → False

section Quat

theorem false_of_quat_of_L2 {R : Type} [Group R] [Finite R] {H' : Subgroup R}
    (eH' : H' ≃* QuaternionGroup 2) {p₁ n₁ : ℕ} [Fact p₁.Prime] (hp₁2 : p₁ ≠ 2) (hn₁ : 0 < n₁)
    (M : Subgroup R) [M.Normal] (hM : Odd (Nat.card M))
    (e : R ⧸ M ≃* PSL(2, GaloisField p₁ n₁)) : False := by
  let ψ : H' →* PSL(2, GaloisField p₁ n₁) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' M).comp H'.subtype)
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro h hh
    rw [MonoidHom.mem_ker] at hh
    have hM' : (h : R) ∈ M := by
      have h1 : QuotientGroup.mk' M (h : R) = 1 := by
        have := congrArg e.symm hh
        simpa [ψ] using this
      exact (QuotientGroup.eq_one_iff _).1 h1
    have h8 : orderOf h ∣ 8 := by
      have := orderOf_dvd_natCard (eH' h)
      rw [Nat.card_eq_fintype_card, QuaternionGroup.card, MulEquiv.orderOf_eq] at this
      exact this
    have hodd : orderOf (⟨(h : R), hM'⟩ : M) ∣ Nat.card M := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe] at hodd
    have h1 : orderOf h = 1 := by
      have hco : Nat.Coprime (orderOf h) 2 := by
        rw [Nat.coprime_two_right]
        exact Odd.of_dvd_nat hM hodd
      exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 3 hco) h8
    rw [orderOf_eq_one_iff] at h1
    rw [h1]
    exact Subgroup.one_mem _
  have hF : GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p₁ n₁)) :=
    ⟨p₁, n₁, Fact.out, Nat.Prime.odd_of_ne_two Fact.out hp₁2, hn₁,
      GaloisField.card p₁ n₁ (by omega)⟩
  exact false_of_quaternion_of_hasDihedralSylowTwo
    (GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model _ hF) ψ.range
    ((MonoidHom.ofInjective hψ).symm.trans eH')

variable {S : Type} [Group S] [Finite S]

theorem false_of_L2_of_le_block {H N R : Subgroup S} (hNH : N ≤ H) (hB : QuatBlock N)
    (hRH : R ≤ H) (hRc : IsPComponent 2 (R.subgroupOf H)) (hRN : R ≤ N) {p₁ n₁ : ℕ}
    [Fact p₁.Prime] (hp₁2 : p₁ ≠ 2) (hn₁ : 0 < n₁) (M : Subgroup R) [M.Normal]
    (hM : Odd (Nat.card M)) (e : R ⧸ M ≃* PSL(2, GaloisField p₁ n₁)) : False := by
  rcases hB with hs | ⟨hq, Q, ⟨eQ⟩⟩
  · exact C.not_le_of_isSolvable hRH hRc hs hRN
  · have hRN' := C.eq_of_le_of_isQuasisimple hRN hNH hRc hq
    subst hRN'
    exact false_of_quat_of_L2 eQ hp₁2 hn₁ M hM e

theorem noL2At_of_blocks {v : MulAut S} {N₁ N₂ : Subgroup S} (hN₁ : N₁ ≤ autFixed v)
    (hN₂ : N₂ ≤ autFixed v) (hs₁ : (N₁.subgroupOf (autFixed v)).IsSubnormal)
    (hs₂ : (N₂.subgroupOf (autFixed v)).IsSubnormal)
    (hperf : ∀ L : Subgroup S, L ≤ autFixed v → ⁅L, L⁆ = L → L ≤ N₁ ⊔ N₂)
    (hB₁ : QuatBlock N₁) (hB₂ : QuatBlock N₂) : NoL2At v := by
  intro R hRH hRc p₁ n₁ _ hp₁2 hn₁ M _ hM ⟨e⟩
  rcases C.le_or_le_of_le_sup hRH hRc hN₁ hN₂ hs₁ hs₂
      (hperf R hRH (C.commutator_eq_of_isPComponent hRH hRc)) with h | h
  · exact false_of_L2_of_le_block hN₁ hB₁ hRH hRc h hp₁2 hn₁ M hM e
  · exact false_of_L2_of_le_block hN₂ hB₂ hRH hRc h hp₁2 hn₁ M hM e

theorem noL2At_of_layer {v : MulAut S} {N : Subgroup S} (hNH : N ≤ autFixed v)
    (hperf : ∀ L : Subgroup S, L ≤ autFixed v → ⁅L, L⁆ = L → L ≤ N) (hB : QuatBlock N) :
    NoL2At v := by
  intro R hRH hRc p₁ n₁ _ hp₁2 hn₁ M _ hM ⟨e⟩
  exact false_of_L2_of_le_block hNH hB hRH hRc
    (hperf R hRH (C.commutator_eq_of_isPComponent hRH hRc)) hp₁2 hn₁ M hM e

end Quat

section Transport

variable {S T : Type} [Group S] [Group T] [Finite S] [Finite T]

omit [Finite S] [Finite T] in
theorem autFixed_congr (θ : S ≃* T) (v : MulAut S) :
    autFixed (MulAut.congr θ v) = (autFixed v).map θ.toMonoidHom := by
  ext y
  constructor
  · intro hy
    refine ⟨θ.symm y, ?_, by simp⟩
    change v (θ.symm y) = θ.symm y
    have h : θ (v (θ.symm y)) = y := hy
    have h' := congrArg θ.symm h
    rwa [MulEquiv.symm_apply_apply] at h'
  · rintro ⟨x, hx, rfl⟩
    change θ (v (θ.symm (θ x))) = θ x
    rw [MulEquiv.symm_apply_apply]
    exact congrArg θ hx

theorem NoL2At.of_congr (θ : S ≃* T) {v : MulAut S} (h : NoL2At (MulAut.congr θ v)) :
    NoL2At v := by
  intro R hRH hRc p₁ n₁ _ hp₁2 hn₁ M _ hM ⟨e⟩
  have hmap := autFixed_congr θ v
  let Φ : autFixed v ≃* autFixed (MulAut.congr θ v) :=
    ((autFixed v).equivMapOfInjective θ.toMonoidHom θ.injective).trans
      (MulEquiv.subgroupCongr hmap.symm)
  have hRc' : IsPComponent 2 ((R.map θ.toMonoidHom).subgroupOf (autFixed (MulAut.congr θ v))) := by
    have h1 := ((CFSG.LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2
      Nat.prime_two Φ).1 (R.subgroupOf (autFixed v))).1 hRc
    have e1 : (R.subgroupOf (autFixed v)).map Φ.toMonoidHom =
        (R.map θ.toMonoidHom).subgroupOf (autFixed (MulAut.congr θ v)) := by
      ext ⟨y, hy⟩
      constructor
      · rintro ⟨⟨x, hxv⟩, hx, hxy⟩
        rw [mem_subgroupOf]
        have : y = θ x := congrArg Subtype.val hxy.symm
        change y ∈ R.map θ.toMonoidHom
        rw [this]
        exact mem_map_of_mem _ hx
      · intro hy'
        rw [mem_subgroupOf] at hy'
        obtain ⟨x, hx, rfl⟩ := hy'
        exact ⟨⟨x, hRH hx⟩, hx, rfl⟩
    rw [← e1]
    exact h1
  have hRH' : R.map θ.toMonoidHom ≤ autFixed (MulAut.congr θ v) := by
    rw [hmap]
    exact map_mono hRH
  let eR : R ≃* R.map θ.toMonoidHom := R.equivMapOfInjective θ.toMonoidHom θ.injective
  have : (M.map eR.toMonoidHom).Normal := Subgroup.Normal.map inferInstance _ eR.surjective
  have hM' : Odd (Nat.card (M.map eR.toMonoidHom)) := by
    rw [Nat.card_congr (M.equivMapOfInjective _ eR.injective).symm.toEquiv]
    exact hM
  exact h _ hRH' hRc' p₁ n₁ hp₁2 hn₁ (M.map eR.toMonoidHom) hM'
    ⟨(QuotientGroup.congr _ _ eR.symm (by
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        change eR.symm (eR z) ∈ M
        rwa [MulEquiv.symm_apply_apply]
      · intro hx
        exact ⟨eR x, ⟨x, hx, rfl⟩, eR.symm_apply_apply x⟩)).trans e⟩

theorem NoL2At.of_conj (α : MulAut S) {v : MulAut S} (h : NoL2At (α * v * α⁻¹)) :
    NoL2At v := by
  refine NoL2At.of_congr α ?_
  have e : MulAut.congr α v = α * v * α⁻¹ := MulEquiv.ext fun _ => rfl
  rw [e]
  exact h

end Transport

section Lift

variable {G : Type*} [Group G] {Z : Subgroup G} [Z.Normal]

@[expose] def cocyc (hZ : Z ≤ center G) (φ : G →* G) : Subgroup G where
  carrier := {g | g⁻¹ * φ g ∈ Z}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change (a * b)⁻¹ * φ (a * b) ∈ Z
    have e : (a * b)⁻¹ * φ (a * b) = (a⁻¹ * φ a) * (b⁻¹ * φ b) := by
      rw [map_mul, mul_inv_rev]
      have hc : ∀ g : G, (a⁻¹ * φ a) * g = g * (a⁻¹ * φ a) := fun g =>
        (mem_center_iff.1 (hZ ha) g).symm
      calc b⁻¹ * a⁻¹ * (φ a * φ b) = b⁻¹ * (a⁻¹ * φ a) * φ b := by group
        _ = (a⁻¹ * φ a) * b⁻¹ * φ b := by rw [← hc b⁻¹]
        _ = (a⁻¹ * φ a) * (b⁻¹ * φ b) := by group
    rw [e]
    exact mul_mem ha hb
  inv_mem' := by
    intro a ha
    change a⁻¹⁻¹ * φ a⁻¹ ∈ Z
    have hc := mem_center_iff.1 (hZ ha)
    have e : a⁻¹⁻¹ * φ a⁻¹ = a * (a⁻¹ * φ a)⁻¹ * a⁻¹ := by
      rw [map_inv]
      group
    rw [e]
    have h1 : (a⁻¹ * φ a)⁻¹ ∈ Z := inv_mem ha
    have h2 := (Subgroup.Normal.conj_mem inferInstance _ h1 a)
    exact h2

theorem mem_cocyc (hZ : Z ≤ center G) (φ : G →* G) {g : G} :
    g ∈ cocyc hZ φ ↔ g⁻¹ * φ g ∈ Z := Iff.rfl

abbrev fixOf (φ : G →* G) : Subgroup G := MonoidHom.eqLocus φ (MonoidHom.id G)

theorem fixOf_le_cocyc (hZ : Z ≤ center G) (φ : G →* G) : fixOf φ ≤ cocyc hZ φ := by
  intro g hg
  have hg' : φ g = g := hg
  rw [mem_cocyc, hg', inv_mul_cancel]
  exact one_mem _

variable {w : MulAut (G ⧸ Z)} {φ : G →* G}

theorem autFixed_eq_map_cocyc (hZ : Z ≤ center G)
    (hw : ∀ g : G, w (g : G ⧸ Z) = (φ g : G ⧸ Z)) :
    autFixed w = (cocyc hZ φ).map (QuotientGroup.mk' Z) := by
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z x
  constructor
  · intro hx
    have hx' : w (g : G ⧸ Z) = (g : G ⧸ Z) := hx
    rw [hw] at hx'
    refine ⟨g, ?_, rfl⟩
    show g⁻¹ * φ g ∈ Z
    exact QuotientGroup.eq.1 hx'.symm
  · rintro ⟨g', hg', hgg'⟩
    change w (QuotientGroup.mk' Z g) = QuotientGroup.mk' Z g
    rw [← hgg']
    change w (g' : G ⧸ Z) = (g' : G ⧸ Z)
    rw [hw]
    exact (QuotientGroup.eq.2 hg').symm

theorem commutator_cocyc_le_fix (hZ : Z ≤ center G) (φ : G →* G) :
    ⁅cocyc hZ φ, cocyc hZ φ⁆ ≤ fixOf φ := by
  rw [commutator_le]
  intro a ha b hb
  change φ ⁅a, b⁆ = ⁅a, b⁆
  have e : ⁅φ a, φ b⁆ = ⁅a * (a⁻¹ * φ a), b * (b⁻¹ * φ b)⁆ := by
    rw [mul_inv_cancel_left, mul_inv_cancel_left]
  rw [map_commutatorElement, e]
  exact PSL.commutatorElement_mul_mem_center a b (hZ ha) (hZ hb)

theorem le_map_commutator_fix_of_perfect (hZ : Z ≤ center G)
    (hw : ∀ g : G, w (g : G ⧸ Z) = (φ g : G ⧸ Z)) {L : Subgroup (G ⧸ Z)}
    (hL : L ≤ autFixed w) (hperf : ⁅L, L⁆ = L) :
    L ≤ ⁅fixOf φ, fixOf φ⁆.map (QuotientGroup.mk' Z) := by
  rw [autFixed_eq_map_cocyc hZ hw] at hL
  have h1 : L ≤ (fixOf φ).map (QuotientGroup.mk' Z) := by
    rw [← hperf]
    refine (commutator_mono hL hL).trans ?_
    rw [← map_commutator]
    exact map_mono (commutator_cocyc_le_fix hZ φ)
  rw [map_commutator, ← hperf]
  exact commutator_mono h1 h1

theorem map_fix_le_autFixed (hZ : Z ≤ center G) (hw : ∀ g : G, w (g : G ⧸ Z) = (φ g : G ⧸ Z))
    {M : Subgroup G} (hM : M ≤ fixOf φ) : M.map (QuotientGroup.mk' Z) ≤ autFixed w := by
  rw [autFixed_eq_map_cocyc hZ hw]
  exact map_mono (hM.trans (fixOf_le_cocyc hZ φ))

theorem isSubnormal_map_of_fix (hZ : Z ≤ center G) (hw : ∀ g : G, w (g : G ⧸ Z) = (φ g : G ⧸ Z))
    {M : Subgroup G} (hM : M ≤ fixOf φ)
    (hn : ∀ B ∈ fixOf φ, ∀ m ∈ M, B * m * B⁻¹ ∈ M) :
    ((M.map (QuotientGroup.mk' Z)).subgroupOf (autFixed w)).IsSubnormal := by
  have hFC := map_fix_le_autFixed hZ hw (le_refl (fixOf φ))
  have hnorm : (((fixOf φ).map (QuotientGroup.mk' Z)).subgroupOf (autFixed w)).Normal := by
    refine ⟨fun a ha b => ?_⟩
    rw [mem_subgroupOf] at ha ⊢
    obtain ⟨m, hm, hma⟩ := ha
    have hb : (b : G ⧸ Z) ∈ (cocyc hZ φ).map (QuotientGroup.mk' Z) := by
      rw [← autFixed_eq_map_cocyc hZ hw]
      exact b.2
    obtain ⟨B, hB, hBb⟩ := hb
    refine ⟨B * m * B⁻¹, ?_, ?_⟩
    ·
      have hm' : φ m = m := hm
      set z := B⁻¹ * φ B with hz
      have hzc : ∀ g, z * g = g * z := fun g => (mem_center_iff.1 (hZ hB) g).symm
      have eB : φ B = B * z := by rw [hz]; group
      change φ (B * m * B⁻¹) = B * m * B⁻¹
      rw [map_mul, map_mul, map_inv, eB, hm']
      calc B * z * m * (B * z)⁻¹ = B * (z * m) * z⁻¹ * B⁻¹ := by group
        _ = B * m * (z * z⁻¹) * B⁻¹ := by rw [hzc m]; group
        _ = B * m * B⁻¹ := by group
    · change QuotientGroup.mk' Z (B * m * B⁻¹) = (b : G ⧸ Z) * (a : G ⧸ Z) * (b : G ⧸ Z)⁻¹
      rw [map_mul, map_mul, map_inv, hBb, hma]
  refine PSL.isSubnormal_subgroupOf_of_normalizes (map_mono hM) ?_ (Normal.isSubnormal hnorm)
  rintro _ ⟨B, hB, rfl⟩ _ ⟨m, hm, rfl⟩
  exact ⟨B * m * B⁻¹, hn B hB m hm, by simp only [map_mul, map_inv]⟩

end Lift

theorem commutator_le_self' {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H := by
  rw [commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

section Layer

variable {G : Type} [Group G] {Z : Subgroup G} [Z.Normal] [Finite (G ⧸ Z)]
  {w : MulAut (G ⧸ Z)} {φ : G →* G}

theorem noL2At_of_fix_layer (hZ : Z ≤ center G) (hw : ∀ g : G, w (g : G ⧸ Z) = (φ g : G ⧸ Z))
    {F : Subgroup G} (hF : F ≤ fixOf φ) (hcomm : ⁅fixOf φ, fixOf φ⁆ ≤ F)
    (hB : QuatBlock (F.map (QuotientGroup.mk' Z))) : NoL2At w :=
  noL2At_of_layer (map_fix_le_autFixed hZ hw hF)
    (fun _ hL hp => (le_map_commutator_fix_of_perfect hZ hw hL hp).trans (map_mono hcomm)) hB

theorem noL2At_of_fix (hZ : Z ≤ center G) (hw : ∀ g : G, w (g : G ⧸ Z) = (φ g : G ⧸ Z))
    (hB : QuatBlock ((fixOf φ).map (QuotientGroup.mk' Z))) : NoL2At w :=
  noL2At_of_fix_layer hZ hw le_rfl (commutator_le_self' _) hB

theorem noL2At_of_fix_blocks (hZ : Z ≤ center G) (hw : ∀ g : G, w (g : G ⧸ Z) = (φ g : G ⧸ Z))
    {F₁ F₂ : Subgroup G} (hF₁ : F₁ ≤ fixOf φ) (hF₂ : F₂ ≤ fixOf φ)
    (hn₁ : ∀ B ∈ fixOf φ, ∀ m ∈ F₁, B * m * B⁻¹ ∈ F₁)
    (hn₂ : ∀ B ∈ fixOf φ, ∀ m ∈ F₂, B * m * B⁻¹ ∈ F₂) (hcomm : ⁅fixOf φ, fixOf φ⁆ ≤ F₁ ⊔ F₂)
    (hB₁ : QuatBlock (F₁.map (QuotientGroup.mk' Z)))
    (hB₂ : QuatBlock (F₂.map (QuotientGroup.mk' Z))) : NoL2At w := by
  refine noL2At_of_blocks (map_fix_le_autFixed hZ hw hF₁) (map_fix_le_autFixed hZ hw hF₂)
    (isSubnormal_map_of_fix hZ hw hF₁ hn₁) (isSubnormal_map_of_fix hZ hw hF₂ hn₂)
    (fun _ hL hp => ?_) hB₁ hB₂
  refine (le_map_commutator_fix_of_perfect hZ hw hL hp).trans ?_
  rw [← Subgroup.map_sup]
  exact map_mono hcomm

end Layer

theorem quatBlock_map_of_pair {S : Type} [Group S] {Z : Subgroup S} [Z.Normal]
    {F : Subgroup S} (hq : IsQuasisimple F) {x y z : S} (hx : x ∈ F) (hy : y ∈ F)
    (hz2 : z ^ 2 = 1) (hxz : x ^ 2 = z) (hyz : y ^ 2 = z) (hxy : x * y = z * (y * x))
    (hzZ : z ∉ Z) : QuatBlock (F.map (QuotientGroup.mk' Z)) := by
  let ψ : F →* F.map (QuotientGroup.mk' Z) :=
    ((QuotientGroup.mk' Z).comp F.subtype).codRestrict (F.map (QuotientGroup.mk' Z))
      (fun g => mem_map_of_mem _ g.2)
  have hzF : z ∈ F := hxz ▸ pow_mem hx 2
  have hψz : ψ ⟨z, hzF⟩ ≠ 1 := by
    intro h1
    apply hzZ
    have h2 : QuotientGroup.mk' Z z = 1 := congrArg Subtype.val h1
    exact (QuotientGroup.eq_one_iff _).1 h2
  obtain ⟨H, ⟨eH⟩⟩ := UnbalancedGS.SymplecticExclusion.exists_quaternion_of_hom ψ
    (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) (z := ⟨z, hzF⟩) (Subtype.ext hz2) (Subtype.ext hxz)
    (Subtype.ext hyz) (Subtype.ext hxy) hψz
  have hr : ((QuotientGroup.mk' Z).comp F.subtype).range = F.map (QuotientGroup.mk' Z) := by
    rw [MonoidHom.range_comp, range_subtype]
  rcases LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hq
      ((QuotientGroup.mk' Z).comp F.subtype) with h0 | h0
  · exfalso
    apply hzZ
    have hm : QuotientGroup.mk' Z z ∈ ((QuotientGroup.mk' Z).comp F.subtype).range :=
      ⟨⟨z, hzF⟩, rfl⟩
    rw [h0, mem_bot] at hm
    exact (QuotientGroup.eq_one_iff _).1 hm
  · rw [hr] at h0
    exact quatBlock_of_quat h0 H eH

end CFSG.ComponentClassification.Burgoyne.Cl
