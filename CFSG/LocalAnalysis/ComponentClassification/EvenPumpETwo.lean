module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpECentre
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpEY
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpDefs
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpAltComp

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup SemidirectProduct CFSG.ComponentClassification.UnbalancedLayer

theorem fusionZStar_eq_of_alt {X : Type*} [Group X] {m : ℕ} (hm : 4 ≤ m)
    (e : X ⧸ pPrimeCore 2 X ≃* alternatingGroup (Fin m)) :
    Open.fusionZStar X = pPrimeCore 2 X := by
  have hZ : center (X ⧸ pPrimeCore 2 X) = ⊥ := by
    have h1 := Subgroup.map_center_eq e
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; omega)] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  rw [Sol78.fusionZStar_eq_comap, hZ, MonoidHom.comap_bot, QuotientGroup.ker_mk']

theorem isPGroup_of_mul_self {G : Type*} [Group G] {Q : Subgroup G} (hQ2 : ∀ q ∈ Q, q * q = 1) :
    IsPGroup 2 Q := fun q => ⟨1, Subtype.ext (by rw [pow_one, sq]; exact hQ2 q q.2)⟩

theorem evenAltAut_le_two (hcore : EvenAltPumpInput) {L : Type} [Group L] [Finite L]
    (hK : SectionRank.IsKGroupCat L) (hq : IsQuasisimple L) (hO : pPrimeCore 2 L = ⊥)
    {Q : Subgroup (MulAut L)} (hQ2 : ∀ q ∈ Q, q * q = 1) (hQc : Nat.card Q ≤ 2)
    {T : Subgroup L} (hTF : T ≤ autFixed Q) (hT : IsPComponent 2 (T.subgroupOf (autFixed Q)))
    (eT : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin 10)) :
    (∃ n : ℕ, Even n ∧ 10 ≤ n ∧ Nonempty (L ≃* alternatingGroup (Fin n))) ∨
      Nonempty (L ⧸ center L ≃* Blueprint.NativeSporadic.Carrier .HN) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 Q := isPGroup_of_mul_self hQ2
  have : Finite (MulAut L) := Finite.of_injective (fun e : MulAut L => e.toEquiv)
    fun _ _ h => MulEquiv.ext fun x => congrArg (fun f : L ≃ L => f x) h
  rcases (show Nat.card Q = 1 ∨ Nat.card Q = 2 by
      have := Nat.card_pos (α := Q)
      omega) with hQ1 | hQ2'
  ·
    have hQb : Q = ⊥ := Subgroup.eq_bot_of_card_eq Q hQ1
    have hFtop : autFixed Q = ⊤ := by
      rw [eq_top_iff]
      intro l _ q hq
      rw [hQb, mem_bot] at hq
      rw [hq]
      rfl
    have hTp : IsPComponent 2 T :=
      (CatalogueBPrimeJoin.pComponent_subnormal_overgroup_iff 2 T (autFixed Q) hTF
        (by rw [hFtop]; exact Subgroup.Normal.isSubnormal inferInstance)).mp hT
    have hTtop : T = ⊤ := by
      rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hq
        ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 T).mp hTp).1 with
        h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := SolMax.alt_nonabelian_of_card (Ω := Fin 10) (by simp)
        obtain ⟨y₁, rfl⟩ := eT.surjective a
        obtain ⟨y₂, rfl⟩ := eT.surjective b
        obtain ⟨t₁, rfl⟩ := QuotientGroup.mk'_surjective _ y₁
        obtain ⟨t₂, rfl⟩ := QuotientGroup.mk'_surjective _ y₂
        apply hab
        have hc : t₁ * t₂ = t₂ * t₁ := Subtype.ext (by
          simp only [Subgroup.coe_mul]
          exact mem_center_iff.mp (h t₂.2) t₁)
        rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hc]
    let eLT : ↥T ≃* L := (MulEquiv.subgroupCongr hTtop).trans Subgroup.topEquiv
    have hTO : pPrimeCore 2 ↥T = ⊥ := by
      have h1 := pPrimeCore_map_iso 2 eLT
      rw [hO] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ eLT.injective).mp h1
    let eT' : ↥T ≃* alternatingGroup (Fin 10) :=
      ((QuotientGroup.quotientMulEquivOfEq hTO).trans QuotientGroup.quotientBot).symm.trans eT
    exact Or.inl ⟨10, ⟨5, rfl⟩, le_rfl, ⟨eLT.symm.trans eT'⟩⟩
  ·
    have := finite_pumpY Q
    obtain ⟨q₀, hq₀⟩ : ∃ q₀ : ↥Q, q₀ ≠ 1 := by
      by_contra h
      push Not at h
      have h1 : Nat.card Q = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (h a).trans (h b).symm⟩, ⟨1⟩⟩
      omega
    have hq₀2 : (q₀ : MulAut L) * q₀ = 1 := hQ2 _ q₀.2
    have hq₀ne : (q₀ : MulAut L) ≠ 1 := fun h => hq₀ (Subtype.ext h)
    have hzp : zpowers q₀ = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, hQ2']
      exact orderOf_eq_prime (by rw [sq]; exact Subtype.ext hq₀2) hq₀
    set x : PumpY Q := inr q₀ with hxdef
    have hx : orderOf x = 2 := orderOf_inr Q hq₀2 hq₀ne
    have hrange : (inr : ↥Q →* PumpY Q).range = zpowers x := by
      rw [MonoidHom.range_eq_map, ← hzp, MonoidHom.map_zpowers]
    have hC : centralizer (((inr : ↥Q →* PumpY Q).range : Subgroup (PumpY Q)) : Set (PumpY Q)) =
        centralizer ({x} : Set (PumpY Q)) := by
      rw [hrange, centralizer_zpowers_eq]
    obtain ⟨hT'C, hT'pc⟩ := isPComponent_centralizer_range Q hTF hT
    rw [hC] at hT'C hT'pc
    set T' := T.map (inl : L →* PumpY Q) with hT'def
    let eT'T : ↥T ≃* ↥T' := T.equivMapOfInjective inl inl_injective
    let eT'q : ↥T' ⧸ pPrimeCore 2 ↥T' ≃* alternatingGroup (Fin 10) :=
      (Sol78.coreQuotCongr eT'T).symm.trans eT
    have hT'Z : Open.fusionZStar ↥T' = pPrimeCore 2 ↥T' := fusionZStar_eq_of_alt (by norm_num) eT'q
    have hex : (Open.fusionZStar ↥T').map T'.subtype ≤ (pPrimeCore 2 ↥T').map T'.subtype ⊔
        (Open.fusionZStar ↥(pumpL Q)).map (pumpL Q).subtype := by
      rw [hT'Z]
      exact le_sup_left
    let eZ : ↥T' ⧸ Open.fusionZStar ↥T' ≃* alternatingGroup (Fin 10) :=
      (QuotientGroup.quotientMulEquivOfEq hT'Z).trans eT'q
    have hxN : x ∈ normalizer ((pumpL Q : Subgroup (PumpY Q)) : Set (PumpY Q)) := by
      have := pumpL_normal Q
      rw [normalizer_eq_top_iff.mpr inferInstance]
      exact mem_top x
    have hT'M : T' ≤ pumpL Q := by
      rintro _ ⟨t, -, rfl⟩
      exact ⟨t, rfl⟩
    obtain ⟨eP⟩ := nonempty_pumpL_fusionZStar_equiv Q hO
    rcases hcore (PumpY Q) (isKGroupCat_pumpY Q hK hQ) (pumpL Q) (isPComponent_pumpL Q hq hO) x
        hx hxN T' hT'M hT'C hT'pc hex 10 ⟨5, rfl⟩ le_rfl ⟨eZ⟩ with
      ⟨m', hm', hm'10, ⟨eM⟩⟩ | ⟨-, ⟨eM⟩⟩
    · let eLZ : L ⧸ center L ≃* alternatingGroup (Fin m') := eP.symm.trans eM
      have hZ := center_eq_bot_of_autFixed_alt hq (by omega) eLZ hQ hTF hT eT
      exact Or.inl ⟨m', hm', hm'10, ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans
        QuotientGroup.quotientBot).symm.trans eLZ⟩⟩
    · exact Or.inr ⟨eP.symm.trans eM⟩

theorem evenAltPumpUpTwo_of_core (hcore : EvenAltPumpInput) :
    ∀ (H : Type) [Group H] [Finite H], SectionRank.IsKGroupCat H →
      ∀ M : Subgroup H, IsPComponent 2 M →
      ∀ E : Subgroup H, IsPGroup 2 E → E ≤ normalizer (M : Set H) →
        (∀ e ∈ E, e ^ 2 ∈ coreActionKernel M) →
        Nat.card E ≤ 2 * Nat.card ↥(E ⊓ coreActionKernel M) →
      ∀ T : Subgroup H, T ≤ M → T ≤ centralizer (E : Set H) →
        IsPComponent 2 (T.subgroupOf (centralizer (E : Set H))) →
        Nonempty (↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin 10)) →
        (∃ n : ℕ, Even n ∧ 10 ≤ n ∧
            Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))) ∨
          Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* Blueprint.NativeSporadic.Carrier .HN) := by
  intro H _ _ hK M hM E hE hEN hE2 hEk T hTM hTE hT ⟨eT⟩
  obtain ⟨L, _, _, hLK, hLq, hLO, ⟨eL⟩, Q, hQ2, hQc, Tb, hTbF, hTb, ⟨eTb⟩⟩ :=
    exists_reduced_pump hK hM hE hEN hE2 hEk hTM hTE hT
  rcases evenAltAut_le_two hcore hLK hLq hLO hQ2 hQc hTbF hTb (eTb.symm.trans eT) with
    ⟨n, hn, h10, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Or.inl ⟨n, hn, h10, ⟨eL.symm.trans e⟩⟩
  · obtain ⟨eMS⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar ↥M
    exact Or.inr ⟨eMS.symm.trans ((Sol78.centerQuotCongr eL).symm.trans e)⟩

end CFSG.ComponentClassification.EvenPump
