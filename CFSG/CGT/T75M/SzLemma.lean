module

public import CFSG.CGT.T75M.SzData
public import CFSG.CGT.T75M.SzOut
public import CFSG.CGT.T75M.SzBorel
public import CFSG.CGT.Timmesfeld75.CentralQuotient
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure

public section

namespace CFSG.CGT.T75M

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.BenderSuzuki
open scoped commutatorElement

section Conj

variable {G : Type} [Group G]

@[expose] def conjMulEquiv (X : Subgroup G) (u : G) (hu : u ∈ Subgroup.normalizer (X : Set G)) :
    ↥X ≃* ↥X where
  toFun x := ⟨u * x * u⁻¹, (Subgroup.mem_normalizer_iff.1 hu x).1 x.2⟩
  invFun x := ⟨u⁻¹ * x * u, by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hu) x).1 x.2
    simpa using this⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

@[simp] theorem conjMulEquiv_apply (X : Subgroup G) (u : G)
    (hu : u ∈ Subgroup.normalizer (X : Set G)) (x : ↥X) :
    ((conjMulEquiv X u hu x : ↥X) : G) = u * x * u⁻¹ := rfl

end Conj


section Main

variable {K : Type} [Group K] [Finite K]

theorem center_eq_bot_of_isBenderGroup (hK : IsBenderGroup K) : Subgroup.center K = ⊥ := by
  have : IsSimpleGroup K := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup hK
  rcases (inferInstance : (Subgroup.center K).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_not_commute hK
    apply hab
    have ha : a ∈ Subgroup.center K := h ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 ha b).symm

end Main


section Pair

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}
  [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal]

set_option quotPrecheck false in
local notation "XQ" => ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)

set_option quotPrecheck false in
local notation "TQ" =>
  (T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))

set_option quotPrecheck false in
local notation "T₁Q" =>
  (T₁.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))

omit [Finite G] hN in
theorem conjMulEquiv_map_subgroupOf {u : G}
    (huX : u ∈ Subgroup.normalizer ((T ⊔ T₁ : Subgroup G) : Set G))
    (huM : u ∈ Subgroup.normalizer ((cfgM T T₁ : Subgroup G) : Set G)) :
    ((cfgM T T₁).subgroupOf (T ⊔ T₁)).map (conjMulEquiv (T ⊔ T₁) u huX).toMonoidHom =
      (cfgM T T₁).subgroupOf (T ⊔ T₁) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact Subgroup.mem_subgroupOf.2 ((Subgroup.mem_normalizer_iff.1 huM z).1
      (Subgroup.mem_subgroupOf.1 hz))
  · intro hy
    refine ⟨(conjMulEquiv (T ⊔ T₁) u huX).symm y, ?_,
      (conjMulEquiv (T ⊔ T₁) u huX).apply_symm_apply y⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    have h1 := Subgroup.mem_subgroupOf.1 hy
    have h2 : (conjMulEquiv (T ⊔ T₁) u huX
        ((conjMulEquiv (T ⊔ T₁) u huX).symm y) : G) ∈ cfgM T T₁ := by
      rw [(conjMulEquiv (T ⊔ T₁) u huX).apply_symm_apply y]; exact h1
    rw [conjMulEquiv_apply] at h2
    exact (Subgroup.mem_normalizer_iff.1 huM _).2 h2

@[expose] def quotConj {u : G} (huX : u ∈ Subgroup.normalizer ((T ⊔ T₁ : Subgroup G) : Set G))
    (huM : u ∈ Subgroup.normalizer ((cfgM T T₁ : Subgroup G) : Set G)) : MulAut XQ :=
  QuotientGroup.congr _ _ (conjMulEquiv (T ⊔ T₁) u huX) (conjMulEquiv_map_subgroupOf huX huM)

omit [Finite G] in
theorem quotConj_mk {u : G} (huX : u ∈ Subgroup.normalizer ((T ⊔ T₁ : Subgroup G) : Set G))
    (huM : u ∈ Subgroup.normalizer ((cfgM T T₁ : Subgroup G) : Set G)) (x : ↥(T ⊔ T₁)) :
    quotConj huX huM (QuotientGroup.mk x) = QuotientGroup.mk (conjMulEquiv (T ⊔ T₁) u huX x) :=
  rfl


theorem exists_comm_of_normalizes (hS : Sec3 T T₁) {a : ℕ}
    (ha : 1 ≤ a) (e : XQ ≃* Sz a) {u : G}
    (huX : u ∈ Subgroup.normalizer ((T ⊔ T₁ : Subgroup G) : Set G))
    (huM : u ∈ Subgroup.normalizer ((cfgM T T₁ : Subgroup G) : Set G))
    (huT : u ∈ Subgroup.normalizer (T : Set G)) (hu2 : u * u = 1) :
    ∃ y ∈ T, (∀ x ∈ T ⊔ T₁, ⁅y * u, x⁆ ∈ cfgM T T₁) ∧
      (u ∈ Subgroup.normalizer (T₁ : Set G) → y ∈ cfgM T T₁) := by
  classical
  have hK : IsBenderGroup XQ := isBenderGroup_of_mulEquiv_sz ha e
  have hTs : StrongWC TQ := strongWC_map hS
  have hT1 : TQ ≠ ⊥ := hS.map_ne_bot
  obtain ⟨Q, hTQ⟩ := (isPGroup_two_of_isElemAbelian hTs.1).exists_le_sylow
  have hTcen := eq_center_of_strongWC hK hTs hT1 Q hTQ
  let σ : MulAut XQ := quotConj huX huM
  have hσ : ∀ x : ↥(T ⊔ T₁), σ (QuotientGroup.mk x) =
      QuotientGroup.mk (conjMulEquiv (T ⊔ T₁) u huX x) := fun x => rfl
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hσσ : σ * σ = 1 := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MulAut.mul_apply, hσ, hσ, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    simp only [conjMulEquiv_apply]
    rw [hu']
    calc u * (u * (x : G) * u) * u = (u * u) * (x : G) * (u * u) := by simp only [mul_assoc]
      _ = x := by rw [hu2]; simp
  obtain ⟨g, hg⟩ := exists_conj_of_mul_self_eq_one (sz_outer_odd ha e) hσσ
  have hgq : ∀ q : XQ, σ q = g * q * g⁻¹ := fun q => by rw [hg]; rfl
  have hgg : g * g = 1 := by
    have hcen : g * g ∈ Subgroup.center XQ := by
      rw [Subgroup.mem_center_iff]
      intro q
      have h2 : g * (g * q * g⁻¹) * g⁻¹ = q := by
        have := congrArg (fun τ : MulAut XQ => τ q) hσσ
        simp only [MulAut.mul_apply, MulAut.one_apply] at this
        rw [hgq q, hgq (g * q * g⁻¹)] at this
        exact this
      have h3 : g * g * q = q * (g * g) := by
        calc g * g * q = (g * (g * q * g⁻¹) * g⁻¹) * (g * g) := by group
          _ = q * (g * g) := by rw [h2]
      exact h3.symm
    rw [center_eq_bot_of_isBenderGroup hK] at hcen
    exact Subgroup.mem_bot.1 hcen
  have key : ∀ S : Subgroup XQ, (∀ h ∈ S, σ h ∈ S) →
      g ∈ Subgroup.normalizer (S : Set XQ) := by
    intro S hS'
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have := hS' h hh
      rwa [hgq h] at this
    · intro hh
      rw [← hgq h] at hh
      have h3 := hS' _ hh
      have h4 : σ (σ h) = h := by
        simpa [MulAut.mul_apply] using congrArg (fun τ : MulAut XQ => τ h) hσσ
      rwa [h4] at h3
  have hσT : ∀ h ∈ TQ, σ h ∈ TQ := by
    rintro _ ⟨t', ht', rfl⟩
    refine ⟨conjMulEquiv (T ⊔ T₁) u huX t', ?_, (hσ t').symm⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, conjMulEquiv_apply]
    exact (Subgroup.mem_normalizer_iff.1 huT _).1
      (Subgroup.mem_subgroupOf.1 (SetLike.mem_coe.1 ht'))
  have hgT : g ∈ Subgroup.normalizer (TQ : Set XQ) := key _ hσT
  have hgQ := mem_normalizer_sylow_of_mem_normalizer hK hTs hT1 Q hTQ hgT
  have hgZ := mem_center_of_mem_normalizer_sylow hK Q hgQ hgg
  rw [← hTcen] at hgZ
  obtain ⟨y', hy'T, hy'g⟩ := hgZ
  have hyX : (y' : G) ∈ T ⊔ T₁ := y'.2
  have hy'T' : (y' : G) ∈ T := Subgroup.mem_subgroupOf.1 (SetLike.mem_coe.1 hy'T)
  refine ⟨(y' : G)⁻¹, T.inv_mem hy'T', ?_, ?_⟩
  · intro x hx
    have h1 := hgq (QuotientGroup.mk ⟨x, hx⟩)
    rw [hσ, ← hy'g] at h1
    have h2 : (QuotientGroup.mk (conjMulEquiv (T ⊔ T₁) u huX ⟨x, hx⟩) : XQ) =
        QuotientGroup.mk (y' * ⟨x, hx⟩ * y'⁻¹) := by
      rw [h1]; rfl
    have h3 := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 h2)
    simp only [conjMulEquiv_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h3
    have h5 : (y' : G)⁻¹ * (((y' : G) * x * (y' : G)⁻¹)⁻¹ * (u * x * u⁻¹)) * ((y' : G)⁻¹)⁻¹ ∈
        cfgM T T₁ := by
      have := hS.cfg.conj_mem_cfgM ((T ⊔ T₁).inv_mem hyX) ((cfgM T T₁).inv_mem h3)
      simpa using this
    have h6 := hS.cfg.conj_mem_cfgM hx h5
    have e : ⁅(y' : G)⁻¹ * u, x⁆ = x * ((y' : G)⁻¹ * (((y' : G) * x * (y' : G)⁻¹)⁻¹ *
        (u * x * u⁻¹)) * ((y' : G)⁻¹)⁻¹) * x⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact h6
  · intro huT₁
    have hg1 : g = 1 := by
      obtain ⟨x₀, hx₀, hT₁eq⟩ := hS.conj
      let k : XQ := QuotientGroup.mk ⟨x₀, hx₀⟩
      have h1 : T₁.subgroupOf (T ⊔ T₁) =
          conjSubgroup (⟨x₀, hx₀⟩ : ↥(T ⊔ T₁)) (T.subgroupOf (T ⊔ T₁)) := by
        rw [conjSubgroup_subgroupOf]
        exact congrArg (fun S : Subgroup G => S.subgroupOf (T ⊔ T₁)) hT₁eq
      have hT₁Q : T₁Q = conjSubgroup k TQ := by
        rw [h1]
        exact map_conjSubgroup (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))
          ⟨x₀, hx₀⟩ (T.subgroupOf (T ⊔ T₁))
      have hT₁s : StrongWC T₁Q := by
        rw [hT₁Q]; exact StrongWC.map_mulEquiv (MulAut.conj k) hTs
      have hT₁1 : T₁Q ≠ ⊥ := by
        rw [hT₁Q]; exact fun h => hT1 (conjSubgroup_eq_bot_iff.1 h)
      let Q₁ : Sylow 2 XQ :=
        Q.mapSurjective (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).surjective
      have hQ₁ : (Q₁ : Subgroup XQ) = conjSubgroup k (Q : Subgroup XQ) :=
        Sylow.coe_mapSurjective (MulAut.conj k).surjective Q
      have hT₁Q₁ : T₁Q ≤ (Q₁ : Subgroup XQ) := by
        rw [hQ₁, hT₁Q]; exact Subgroup.map_mono hTQ
      have hσT₁ : ∀ h ∈ T₁Q, σ h ∈ T₁Q := by
        rintro _ ⟨t', ht', rfl⟩
        refine ⟨conjMulEquiv (T ⊔ T₁) u huX t', ?_, (hσ t').symm⟩
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, conjMulEquiv_apply]
        exact (Subgroup.mem_normalizer_iff.1 huT₁ _).1
          (Subgroup.mem_subgroupOf.1 (SetLike.mem_coe.1 ht'))
      have hgT₁ : g ∈ Subgroup.normalizer (T₁Q : Set XQ) := key _ hσT₁
      have hgQ₁ := mem_normalizer_sylow_of_mem_normalizer hK hT₁s hT₁1 Q₁ hT₁Q₁ hgT₁
      have hkQ : k ∉ Subgroup.normalizer (Q : Set XQ) := by
        intro hk
        have hiff : ∀ z, z ∈ TQ ↔ z ∈ (Q : Subgroup XQ) ∧ ∀ q ∈ (Q : Subgroup XQ), Commute q z := by
          intro z
          constructor
          · intro hz
            refine ⟨hTQ hz, fun q hq => ?_⟩
            exact (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hK Q
              (hTQ hz) (by rw [← pow_two]; exact hTs.1.2 z hz) q hq).symm
          · rintro ⟨hzQ, hzc⟩
            obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hT1
            exact mem_of_commute_sylow_of_strongWC hK hTs ht (fun h => ht1 (Subtype.ext h)) Q hTQ
              hzQ hzc
        have hkT := mem_normalizer_of_forall_mem_iff (Q := (Q : Subgroup XQ)) hiff hk
        have : conjSubgroup k TQ = TQ := mem_normalizer_iff_conjSubgroup_eq.1 hkT
        exact hS.map_ne_map (hT₁Q.trans this)
      have hgQ₁' : g ∈ Subgroup.normalizer
          ((conjSubgroup k (Q : Subgroup XQ) : Subgroup XQ) : Set XQ) := by
        rw [← hQ₁]; exact hgQ₁
      exact eq_one_of_mem_normalizer_two_sylows hK Q hkQ hgQ hgQ₁' hgg
    have hy'M : (y' : G) ∈ cfgM T T₁ :=
      Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff y').1 (hy'g.trans hg1))
    simpa using (cfgM T T₁).inv_mem hy'M

end Pair

end CFSG.CGT.T75M
