module

import CFSG.GroupTheory.TwoGroupFixedPointQuotient
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpRigid

open Subgroup

section Step4

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_forall {H : Subgroup G} {g : G} (h : ∀ y ∈ H, g * y * g⁻¹ ∈ H) :
    g ∈ normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have hcard : Nat.card ↥H ≤ Nat.card ↥(H.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have heq : H.map (MulAut.conj g).toMonoidHom = H := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  rw [← heq] at hy
  obtain ⟨y', hy', hyy⟩ := hy
  have : y' = y := by
    have h1 : g * y' * g⁻¹ = g * y * g⁻¹ := hyy
    exact mul_left_cancel (mul_right_cancel h1)
  rw [← this]
  exact hy'

theorem exists_normalizing_sq {Q R : Subgroup G} (hQ : IsPGroup 2 Q) (hRQ : R ≤ Q) (hne : R ≠ Q) :
    ∃ s ∈ Q, s ∈ normalizer (R : Set G) ∧ s ∉ R ∧ s * s ∈ R := by
  have hnil : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hlt : R.subgroupOf Q < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hne
    apply le_antisymm hRQ
    intro q hq
    have : (⟨q, hq⟩ : ↥Q) ∈ R.subgroupOf Q := by
      rw [h]
      exact mem_top _
    exact this
  obtain ⟨s₀, hs₀N, hs₀R⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hs₀Q : (s₀ : G) ∈ Q := s₀.2
  have hs₀R' : (s₀ : G) ∉ R := fun h => hs₀R h
  have hs₀norm : (s₀ : G) ∈ normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff] at hs₀N ⊢
    intro g
    by_cases hgQ : g ∈ Q
    · have := hs₀N ⟨g, hgQ⟩
      exact this
    · have h1 : g ∉ R := fun h => hgQ (hRQ h)
      have h2 : (s₀ : G) * g * (s₀ : G)⁻¹ ∉ R := by
        intro h
        apply hgQ
        have h3 := hRQ h
        have : g = (s₀ : G)⁻¹ * ((s₀ : G) * g * (s₀ : G)⁻¹) * (s₀ : G) := by group
        rw [this]
        exact mul_mem (mul_mem (inv_mem hs₀Q) h3) hs₀Q
      exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  have hex : ∃ m : ℕ, (s₀ : G) ^ (2 ^ m) ∈ R := by
    obtain ⟨n, hn⟩ := hQ ⟨(s₀ : G), hs₀Q⟩
    refine ⟨n, ?_⟩
    have : (s₀ : G) ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    rw [this]
    exact one_mem R
  classical
  have hm : (s₀ : G) ^ (2 ^ Nat.find hex) ∈ R := Nat.find_spec hex
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hm
    exact hs₀R' hm
  obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hmin : (s₀ : G) ^ (2 ^ m') ∉ R := Nat.find_min hex (by omega)
  refine ⟨(s₀ : G) ^ (2 ^ m'), Subgroup.pow_mem _ hs₀Q _, ?_, hmin, ?_⟩
  · exact Subgroup.pow_mem _ hs₀norm _ |> fun h => by simpa using h
  · rw [hm'] at hm
    rw [← pow_two, ← pow_mul, ← pow_succ]
    exact hm

omit [Finite G] in
theorem relIndex_eq_two_of_cov {R R₀ : Subgroup G} {x : G} (hxR : x ∈ R)
    (hxc : ∀ r ∈ R, r * x = x * r) (hxR₀ : x ∉ R₀) (hcov : ∀ r ∈ R, r ∈ R₀ ∨ x * r ∈ R₀) :
    R₀.relIndex R = 2 := by
  show (R₀.subgroupOf R).index = 2
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨x, hxR⟩, fun b => ?_⟩
  have hxb : x * (b : G) = (b : G) * x := (hxc _ b.2).symm
  by_cases hb : (b : G) ∈ R₀
  · have h1 : (b : G) * x ∉ R₀ := by
      intro h
      apply hxR₀
      have : x = (b : G)⁻¹ * ((b : G) * x) := by group
      rw [this]
      exact mul_mem (inv_mem hb) h
    exact Or.inr ⟨hb, fun h => h1 h⟩
  · have h1 : (b : G) * x ∈ R₀ := by
      rcases hcov b b.2 with h | h
      · exact absurd h hb
      · rw [← hxb]
        exact h
    exact Or.inl ⟨h1, hb⟩

theorem exists_actor_fixed_normalizing_sq {Q R : Subgroup G} {y : G}
    (hQ : IsPGroup 2 Q) (hRQ : R ≤ Q) (hne : R ≠ Q)
    (hyo : orderOf y = 2) (hyQ : y ∈ Subgroup.normalizer (Q : Set G))
    (hyR : y ∈ Subgroup.normalizer (R : Set G)) :
    ∃ s ∈ Q, s ∈ Subgroup.normalizer (R : Set G) ∧ s ∉ R ∧ s * s ∈ R ∧
      ∃ r ∈ R, y * s * y⁻¹ = s * r := by
  let NQ : Subgroup G := Q ⊓ Subgroup.normalizer (R : Set G)
  have hNQ_Q : NQ ≤ Q := inf_le_left
  have hNQnormR : NQ ≤ Subgroup.normalizer (R : Set G) := inf_le_right
  have hR_NQ : R ≤ NQ := fun r hr => ⟨hRQ hr, Subgroup.le_normalizer hr⟩
  have hNQp : IsPGroup 2 NQ := hQ.to_le hNQ_Q
  have hNQ_ne_R : NQ ≠ R := by
    obtain ⟨s0, hs0Q, hs0N, hs0R, -⟩ := exists_normalizing_sq hQ hRQ hne
    intro h
    exact hs0R (by rw [← h]; exact ⟨hs0Q, hs0N⟩)
  have hyQmap : Q.map (MulAut.conj y).toMonoidHom = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hyQ
  have hyRmap : R.map (MulAut.conj y).toMonoidHom = R :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hyR
  have hyNQmap : NQ.map (MulAut.conj y).toMonoidHom = NQ := by
    dsimp only [NQ]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj y).injective, hyQmap,
      Subgroup.map_equiv_normalizer_eq R (MulAut.conj y), hyRmap]
  have hyNQ : y ∈ Subgroup.normalizer (NQ : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hyNQmap
  let A : Subgroup G := Subgroup.zpowers y
  have hA : IsPGroup 2 A := by
    dsimp only [A]
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
  have hA_NQ : A ≤ Subgroup.normalizer (NQ : Set G) := Subgroup.zpowers_le.mpr hyNQ
  have hA_R : A ≤ Subgroup.normalizer (R : Set G) := Subgroup.zpowers_le.mpr hyR
  obtain ⟨r, hrNQ, hrR, hfixr⟩ :=
    CFSG.exists_fixed_coset_of_isPGroup_two (A := A) (R := NQ) (T := R)
      hA hNQp hA_NQ hA_R hR_NQ (lt_of_le_of_ne hR_NQ hNQ_ne_R.symm)
  let F : Subgroup ↥NQ :=
    { carrier := {x | ∀ a : A, (a : G) * (x : G) * (a : G)⁻¹ * (x : G)⁻¹ ∈ R}
      one_mem' := by
        intro a
        simp
      mul_mem' := by
        intro x z hx hz a
        have hx' : (a : G) * (x : G) * (a : G)⁻¹ * (x : G)⁻¹ ∈ R := hx a
        have hz' : (a : G) * (z : G) * (a : G)⁻¹ * (z : G)⁻¹ ∈ R := hz a
        have hxN : (x : G) ∈ Subgroup.normalizer (R : Set G) := hNQnormR x.2
        have h1 : (a : G) * ((x * z : ↥NQ) : G) * (a : G)⁻¹ * ((x * z : ↥NQ) : G)⁻¹ =
            ((a : G) * (x : G) * (a : G)⁻¹ * (x : G)⁻¹) *
              ((x : G) * ((a : G) * (z : G) * (a : G)⁻¹ * (z : G)⁻¹) * (x : G)⁻¹) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [h1]
        exact R.mul_mem hx' ((Subgroup.mem_normalizer_iff.mp hxN _).mp hz')
      inv_mem' := by
        intro x hx a
        have hx' : (a : G) * (x : G) * (a : G)⁻¹ * (x : G)⁻¹ ∈ R := hx a
        have hxN : (x : G) ∈ Subgroup.normalizer (R : Set G) := hNQnormR x.2
        have h1 : (a : G) * ((x⁻¹ : ↥NQ) : G) * (a : G)⁻¹ * ((x⁻¹ : ↥NQ) : G)⁻¹ =
            (x : G)⁻¹ * ((a : G) * (x : G) * (a : G)⁻¹ * (x : G)⁻¹)⁻¹ * (x : G) := by
          simp only [Subgroup.coe_inv, inv_inv]
          group
        rw [h1]
        simpa only [inv_inv] using
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) _).mp
            (Subgroup.inv_mem _ hx') }
  have hRF : R.subgroupOf NQ ≤ F := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    intro a
    have hxR : (x : G) ∈ R := hx
    have haN : (a : G) ∈ Subgroup.normalizer (R : Set G) := hA_R a.2
    have hax : (a : G) * (x : G) * (a : G)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp haN (x : G)).mp hxR
    exact R.mul_mem hax (R.inv_mem hxR)
  have hF_ne : F ≠ R.subgroupOf NQ := by
    intro h
    have hrF : (⟨r, hrNQ⟩ : ↥NQ) ∈ F := fun a => hfixr a a.2
    have : (⟨r, hrNQ⟩ : ↥NQ) ∈ R.subgroupOf NQ := by rw [← h]; exact hrF
    exact hrR (Subgroup.mem_subgroupOf.mp this)
  have hFp : IsPGroup 2 F := hNQp.to_subgroup F
  obtain ⟨sF, hsF, -, hsFR, hsFsq⟩ :=
    exists_normalizing_sq (G := ↥NQ) (Q := F) (R := R.subgroupOf NQ)
      hFp hRF hF_ne.symm
  let s : G := (sF : ↥NQ)
  have hsNQ : s ∈ NQ := sF.2
  have hsQ : s ∈ Q := hNQ_Q hsNQ
  have hsN : s ∈ Subgroup.normalizer (R : Set G) := hNQnormR hsNQ
  have hsFy : y * s * y⁻¹ * s⁻¹ ∈ R := hsF ⟨y, Subgroup.mem_zpowers y⟩
  have hsR : s ∉ R := by
    intro hs
    exact hsFR (Subgroup.mem_subgroupOf.mpr hs)
  have hs2 : s * s ∈ R := by
    have := Subgroup.mem_subgroupOf.mp hsFsq
    simpa [s] using this
  refine ⟨s, hsQ, hsN, hsR, hs2, ?_⟩
  refine ⟨s⁻¹ * (y * s * y⁻¹ * s⁻¹) * s, ?_, ?_⟩
  · simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsN) _).mp hsFy
  · group

theorem card_R_eq_four_of_actorInvolution {Q R R0 : Subgroup G} {x t y : G}
    (hQ : IsPGroup 2 Q) (hRQ : R ≤ Q) (hne : R ≠ Q)
    (hR0R : R0 ≤ R) (hxR : x ∈ R) (hxo : orderOf x = 2)
    (hxc : ∀ q ∈ Q, q * x = x * q) (hxR0 : x ∉ R0)
    (hcov : ∀ r ∈ R, r ∈ R0 ∨ x * r ∈ R0)
    (htR0 : t ∈ R0) (hto : orderOf t = 2)
    (hyo : orderOf y = 2)
    (hyQ : y ∈ Subgroup.normalizer (Q : Set G))
    (hyR : y ∈ Subgroup.normalizer (R : Set G))
    (hyR0 : y ∈ Subgroup.normalizer (R0 : Set G))
    (hmax : ∀ w ∈ R0, orderOf w = 2 → (∀ r ∈ R, w * r = r * w) →
      w * y = y * w → ∀ g ∈ Q, g * w = w * g → g ∈ R) :
    Nat.card ↥R = 4 ∧ ∀ r ∈ R0, r = 1 ∨ r = t := by
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hxo, sq] at this
  have hidx : (R0.subgroupOf R).index = 2 :=
    relIndex_eq_two_of_cov hxR (fun r hr => hxc r (hRQ hr)) hxR0 hcov
  have hnormR0 : ∀ r ∈ R, ∀ ρ ∈ R0, r * ρ * r⁻¹ ∈ R0 := by
    have hn := Subgroup.normal_of_index_eq_two hidx
    intro r hr ρ hρ
    have := hn.conj_mem ⟨ρ, hR0R hρ⟩ hρ ⟨r, hr⟩
    exact this
  obtain ⟨s, hsQ, hsN, hsR, hsq, r, hrR, hysr⟩ :=
    exists_actor_fixed_normalizing_sq hQ hRQ hne hyo hyQ hyR
  have hsfwd : ∀ r ∈ R, s * r * s⁻¹ ∈ R := fun r hr =>
    (Subgroup.mem_normalizer_iff.mp hsN r).mp hr
  have hsinv : ∀ r ∈ R, s⁻¹ * r * s ∈ R := by
    intro r hr
    exact (Subgroup.mem_normalizer_iff.mp hsN (s⁻¹ * r * s)).mpr (by
      have : s * (s⁻¹ * r * s) * s⁻¹ = r := by group
      rwa [this])
  set R0s : Subgroup G := R0.map (MulAut.conj s).toMonoidHom with hR0s
  have hR0sR : R0s ≤ R := by
    rintro _ ⟨ρ, hρ, rfl⟩
    exact hsfwd ρ (hR0R hρ)
  have hmemR0s : ∀ z, z ∈ R0s ↔ s⁻¹ * z * s ∈ R0 := by
    intro z
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      have : s⁻¹ * (MulAut.conj s).toMonoidHom ρ * s = ρ := by
        simp [MulAut.conj_apply]; group
      rw [this]
      exact hρ
    · intro h
      exact ⟨s⁻¹ * z * s, h, by simp [MulAut.conj_apply]; group⟩
  set R1 : Subgroup G := R0 ⊓ R0s with hR1
  have hR1R : R1 ≤ R := inf_le_left.trans hR0R
  have hRnorm : ∀ r ∈ R, r ∈ normalizer (R1 : Set G) := by
    intro r hr
    refine mem_normalizer_of_forall fun z hz => ?_
    obtain ⟨hz0, hzs⟩ := hz
    refine ⟨hnormR0 r hr z hz0, (hmemR0s _).mpr ?_⟩
    have h1 : s⁻¹ * (r * z * r⁻¹) * s =
        (s⁻¹ * r * s) * (s⁻¹ * z * s) * (s⁻¹ * r * s)⁻¹ := by group
    rw [h1]
    exact hnormR0 _ (hsinv r hr) _ ((hmemR0s z).mp hzs)
  have hsnorm : s ∈ normalizer (R1 : Set G) := by
    refine mem_normalizer_of_forall fun z hz => ?_
    obtain ⟨hz0, hzs⟩ := hz
    refine ⟨?_, (hmemR0s _).mpr ?_⟩
    · have h1 : s * z * s⁻¹ = (s * s) * (s⁻¹ * z * s) * (s * s)⁻¹ := by group
      rw [h1]
      exact hnormR0 _ hsq _ ((hmemR0s z).mp hzs)
    · have : s⁻¹ * (s * z * s⁻¹) * s = z := by group
      rw [this]
      exact hz0
  have hyR0s : y ∈ normalizer (R0s : Set G) := by
    refine mem_normalizer_of_forall fun z hz => ?_
    have hz0 : s⁻¹ * z * s ∈ R0 := (hmemR0s z).mp hz
    have hρ : y * (s⁻¹ * z * s) * y⁻¹ ∈ R0 :=
      (Subgroup.mem_normalizer_iff.mp hyR0 (s⁻¹ * z * s)).mp hz0
    refine (hmemR0s (y * z * y⁻¹)).mpr ?_
    have hconj : y * z * y⁻¹ =
        (s * r) * (y * (s⁻¹ * z * s) * y⁻¹) * (s * r)⁻¹ := by
      have hz_eq : z = s * (s⁻¹ * z * s) * s⁻¹ := by group
      calc y * z * y⁻¹
          = y * (s * (s⁻¹ * z * s) * s⁻¹) * y⁻¹ := by
              conv_lhs => rw [hz_eq]
        _ = (y * s * y⁻¹) * (y * (s⁻¹ * z * s) * y⁻¹) * (y * s * y⁻¹)⁻¹ := by
              group
        _ = (s * r) * (y * (s⁻¹ * z * s) * y⁻¹) * (s * r)⁻¹ := by rw [hysr]
    rw [hconj]
    have hcalc : s⁻¹ * ((s * r) * (y * (s⁻¹ * z * s) * y⁻¹) * (s * r)⁻¹) * s =
        r * (y * (s⁻¹ * z * s) * y⁻¹) * r⁻¹ := by group
    rw [hcalc]
    exact hnormR0 r hrR _ hρ
  have hyR1 : y ∈ normalizer (R1 : Set G) := by
    refine mem_normalizer_of_forall fun z hz => ?_
    exact ⟨(Subgroup.mem_normalizer_iff.mp hyR0 z).mp hz.1,
      (Subgroup.mem_normalizer_iff.mp hyR0s z).mp hz.2⟩
  set T : Subgroup G := R ⊔ Subgroup.zpowers s with hT
  have hTQ : T ≤ Q := sup_le hRQ (Subgroup.zpowers_le.mpr hsQ)
  have hTp : IsPGroup 2 T := hQ.to_le hTQ
  have hTnorm : T ≤ normalizer (R1 : Set G) :=
    sup_le (fun r hr => hRnorm r hr) (Subgroup.zpowers_le.mpr hsnorm)
  have hyRmap : R.map (MulAut.conj y).toMonoidHom = R :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hyR
  have hTmap_le : T.map (MulAut.conj y).toMonoidHom ≤ T := by
    dsimp only [T]
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hyRmap]
    refine sup_le le_sup_left ?_
    have hyconj : (MulEquiv.toMonoidHom (MulAut.conj y)) s = y * s * y⁻¹ := rfl
    rw [hyconj, hysr]
    exact Subgroup.zpowers_le.mpr
      (mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
        (Subgroup.mem_sup_left hrR))
  have hTmap : T.map (MulAut.conj y).toMonoidHom = T := by
    refine Subgroup.eq_of_le_of_card_ge hTmap_le ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
  have hyT : y ∈ normalizer (T : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hTmap
  let A : Subgroup G := Subgroup.zpowers y
  have hA : IsPGroup 2 A := by
    dsimp only [A]
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
  have hA_T : A ≤ normalizer (T : Set G) := by
    dsimp only [A]
    exact Subgroup.zpowers_le.mpr hyT
  let U : Subgroup G := A ⊔ T
  have hUp : IsPGroup 2 U := by
    dsimp only [U]
    exact IsPGroup.to_sup_of_normal_right' hA hTp hA_T
  have hAnorm : A ≤ normalizer (R1 : Set G) := by
    dsimp only [A]
    exact Subgroup.zpowers_le.mpr hyR1
  have hUnorm : U ≤ normalizer (R1 : Set G) := sup_le hAnorm hTnorm
  have hR_U : R ≤ U := le_sup_left.trans le_sup_right
  have hR1bot : R1 = ⊥ := by
    by_contra hR1ne
    have hR1U : R1 ≤ U := hR1R.trans hR_U
    have hnormal : (R1.subgroupOf U).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hUnorm
    have hne1 : R1.subgroupOf U ≠ ⊥ := by
      intro hbot
      apply hR1ne
      rw [eq_bot_iff]
      intro z hz
      have : (⟨z, hR1U hz⟩ : ↥U) ∈ R1.subgroupOf U := hz
      rw [hbot, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    haveI : Group.IsNilpotent ↥U := hUp.isNilpotent
    have hcent := Group.IsNilpotent.inf_center_ne_bot_of_normal hne1
    obtain ⟨v0, hv0, hv0ne⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hcent
    have hv0R1 : (v0 : G) ∈ R1 := Subgroup.mem_subgroupOf.mp hv0.1
    have hv0cent : v0 ∈ Subgroup.center ↥U := hv0.2
    obtain ⟨k, hk⟩ := hUp.exists_orderOf_eq_pow v0
    have hk0 : k ≠ 0 := by
      intro hk0
      exact hv0ne (orderOf_eq_one_iff.mp (by rw [hk, hk0, pow_zero]))
    let w0 : ↥U := v0 ^ (orderOf v0 / 2)
    have hw0ord : orderOf w0 = 2 := by
      dsimp only [w0]
      exact orderOf_pow_orderOf_div (by rw [hk]; positivity)
        (by rw [hk]; exact dvd_pow_self 2 hk0)
    have hw0R1 : w0 ∈ R1.subgroupOf U := Subgroup.pow_mem _ hv0.1 _
    have hw0cent : w0 ∈ Subgroup.center ↥U := Subgroup.pow_mem _ hv0cent _
    let w : G := (w0 : ↥U)
    have hwR1 : w ∈ R1 := Subgroup.mem_subgroupOf.mp hw0R1
    have hwo : orderOf w = 2 := by
      rw [show w = (w0 : ↥U) from rfl, Subgroup.orderOf_coe]
      exact hw0ord
    have hwR0 : w ∈ R0 := (inf_le_left : R1 ≤ R0) hwR1
    have hwR : ∀ z ∈ R, w * z = z * w := by
      intro z hz
      have := congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hw0cent ⟨z, hR_U hz⟩)
      simpa [w] using this.symm
    have hyU : y ∈ U := by
      dsimp only [U, A]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
    have hwy : w * y = y * w := by
      have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hw0cent ⟨y, hyU⟩)
      simpa [w] using this.symm
    have hsU : s ∈ U := by
      dsimp only [U, T]
      exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
    have hsW : s * w = w * s := by
      have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hw0cent ⟨s, hsU⟩)
      simpa [w] using this
    exact hsR (hmax w hwR0 hwo hwR hwy s hsQ hsW)
  have hcardR : Nat.card ↥R = 2 * Nat.card ↥R0 := by
    have h := Subgroup.relIndex_mul_card R0 R
    rw [inf_eq_left.mpr hR0R] at h
    have h2 : R0.relIndex R = 2 := hidx
    rw [h2] at h
    exact h.symm
  have hcardR0s : Nat.card ↥R0s = Nat.card ↥R0 :=
    Subgroup.card_map_of_injective (MulAut.conj s).injective
  have hinj : Function.Injective (fun p : ↥R0 × ↥R0s =>
      (⟨(p.1 : G) * p.2, mul_mem (hR0R p.1.2) (hR0sR p.2.2)⟩ : ↥R)) := by
    intro p p' hpp
    have h1 : (p.1 : G) * p.2 = p'.1 * p'.2 := congrArg Subtype.val hpp
    have h2 : (p'.1 : G)⁻¹ * p.1 = p'.2 * (p.2 : G)⁻¹ := by
      calc (p'.1 : G)⁻¹ * p.1 = (p'.1 : G)⁻¹ * (p.1 * p.2) * (p.2 : G)⁻¹ := by group
        _ = (p'.1 : G)⁻¹ * (p'.1 * p'.2) * (p.2 : G)⁻¹ := by rw [h1]
        _ = p'.2 * (p.2 : G)⁻¹ := by group
    have h3 : (p'.1 : G)⁻¹ * p.1 ∈ R1 := ⟨mul_mem (Subgroup.inv_mem _ p'.1.2) p.1.2, by
      rw [h2]
      exact mul_mem p'.2.2 (Subgroup.inv_mem _ p.2.2)⟩
    rw [hR1bot, Subgroup.mem_bot] at h3
    have h4 : (p.1 : G) = p'.1 := inv_mul_eq_one.mp h3 |>.symm
    have h5 : (p.2 : G) = p'.2 := by
      have : (p'.2 : G) * (p.2 : G)⁻¹ = 1 := by rw [← h2]; exact h3
      exact (mul_inv_eq_one.mp this).symm
    exact Prod.ext (Subtype.ext h4) (Subtype.ext h5)
  have hle : Nat.card ↥R0 * Nat.card ↥R0 ≤ Nat.card ↥R := by
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_prod, hcardR0s] at this
  have hposR0 : 0 < Nat.card ↥R0 := Nat.card_pos
  have hR0le : Nat.card ↥R0 ≤ 2 := by
    rw [hcardR] at hle
    nlinarith
  have hR0ge : 2 ≤ Nat.card ↥R0 := by
    have h1 : orderOf (⟨t, htR0⟩ : ↥R0) ∣ Nat.card ↥R0 := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hto] at h1
    exact Nat.le_of_dvd hposR0 h1
  have hR02 : Nat.card ↥R0 = 2 := le_antisymm hR0le hR0ge
  refine ⟨by rw [hcardR, hR02], fun r hr => ?_⟩
  have hzp : Subgroup.zpowers t = R0 := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr htR0) ?_
    rw [hR02, Nat.card_zpowers, hto]
  rw [← hzp] at hr
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
  rw [← zpow_mod_orderOf, hto]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    have : k % ((2 : ℕ) : ℤ) = 0 := by exact_mod_cast h
    rw [this, zpow_zero]
  · right
    have : k % ((2 : ℕ) : ℤ) = 1 := by exact_mod_cast h
    rw [this, zpow_one]

end Step4

end CFSG.GH74.GLS.C3.Layer1.PumpRigid
