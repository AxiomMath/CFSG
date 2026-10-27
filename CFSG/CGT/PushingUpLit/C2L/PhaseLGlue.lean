module

public import CFSG.CGT.PushingUpLit.C2L.ClassTwoFacts
public import CFSG.CGT.PushingUpLit.C2L.Gomi41
import CFSG.CGT.PushingUpLit.T2K.SixD
public import CFSG.CGT.PushingUpLit.C2L.Gomi42

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
  CFSG.CGT.PushingUpLit.T2KSW
open CFSG.RankThree.PartOne (omegaOneCenterIn)
open scoped commutatorElement
open T2KSW.Aux

variable {G : Type} [Group G]

section Elementary

variable [Finite G]

theorem exists_mem_not_mem_normalizer {K P : Subgroup G} (hP : IsSylowOf 2 P K)
    (hK : ¬ TwoClosed K) : ∃ a ∈ K, a ∉ Subgroup.normalizer (P : Set G) := by
  have hnc := hK
  rw [twoClosed_iff_forall_eq] at hnc
  push Not at hnc
  obtain ⟨S₁, S₂, hS₁, hS₂, hne⟩ := hnc
  obtain ⟨S, hS, hSP⟩ : ∃ S, IsSylowOf 2 S K ∧ S ≠ P := by
    by_cases h1 : S₁ = P
    · exact ⟨S₂, hS₂, fun h2 => hne (h1.trans h2.symm)⟩
    · exact ⟨S₁, hS₁, h1⟩
  obtain ⟨a, haK, rfl⟩ := exists_eq_map_conj_of_isSylowOf hP hS
  exact ⟨a, haK, fun h => hSP (Subgroup.mem_normalizer_iff_map_conj_eq.1 h)⟩

theorem isOtherSylow_map_conj {P D : Subgroup G} (hP : IsSylowOf 2 P ⊤)
    (hPD : P ≤ Subgroup.normalizer (D : Set G)) {a : G}
    (ha : a ∈ Subgroup.normalizer (D : Set G)) (hna : a ∉ Subgroup.normalizer (P : Set G)) :
    IsOtherSylow P D (P.map (MulAut.conj a).toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · have h1 := (isSylowOf_map_conj_iff (A := P) (B := Subgroup.normalizer (D : Set G)) a).2
      (hP.of_le hPD le_top)
    have hN : (Subgroup.normalizer (D : Set G)).map (MulAut.conj a).toMonoidHom =
        Subgroup.normalizer (D : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer ha)
    rwa [hN] at h1
  · rw [inf_eq_left.2 hPD]
    intro h
    exact hna (Subgroup.mem_normalizer_iff_map_conj_eq.2 h)

end Elementary

omit [Group G] in
theorem GomiE'.symm [Group G] {P D₁ D₂ : Subgroup G} (h : GomiE' P D₁ D₂) : GomiE' P D₂ D₁ :=
  ⟨h.1.symm, fun Q₁ Q₂ h1 h2 => (h.2 Q₂ Q₁ h2 h1).symm⟩

theorem omegaOneCenterIn_map_conj (Q : Subgroup G) (g : G) :
    omegaOneCenterIn (Q.map (MulAut.conj g).toMonoidHom) =
      (omegaOneCenterIn Q).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_omegaOneCenterIn_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hc, h2⟩
    refine ⟨y, mem_omegaOneCenterIn_iff.2 ⟨hy, fun q hq => ?_, ?_⟩, rfl⟩
    · have := hc _ ⟨q, hq, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      calc q * y = g⁻¹ * ((g * q * g⁻¹) * (g * y * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * y * g⁻¹) * (g * q * g⁻¹)) * g := by rw [this]
        _ = y * q := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h2
      calc y * y = g⁻¹ * (g * y * g⁻¹ * (g * y * g⁻¹)) * g := by group
        _ = 1 := by rw [h2]; group
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyQ, hyc, hy2⟩ := mem_omegaOneCenterIn_iff.1 hy
    refine ⟨⟨y, hyQ, rfl⟩, fun z hz => ?_, ?_⟩
    · obtain ⟨q, hq, rfl⟩ := hz
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * q * g⁻¹ * (g * y * g⁻¹) = g * (q * y) * g⁻¹ := by group
        _ = g * (y * q) * g⁻¹ := by rw [hyc q hq]
        _ = g * y * g⁻¹ * (g * q * g⁻¹) := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
        _ = 1 := by rw [hy2]; group

theorem omegaOneCenterIn_eq_zc {Q : Subgroup G} (h : ∀ z ∈ Q ⊓ Subgroup.centralizer (Q : Set G),
    z * z = 1) : omegaOneCenterIn Q = Q ⊓ Subgroup.centralizer (Q : Set G) := by
  ext x
  rw [mem_omegaOneCenterIn_iff, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact ⟨fun hx => ⟨hx.1, hx.2.1⟩, fun hx => ⟨hx.1, hx.2, h x (Subgroup.mem_inf.2 ⟨hx.1,
    Subgroup.mem_centralizer_iff.2 hx.2⟩)⟩⟩

structure Gomi46Data (G : Type) [Group G] : Prop where
  l47 : ∀ P D₁ D₂ : Subgroup G, IsSylowOf 2 P ⊤ → GomiE P D₁ D₂ → GomiE' P D₁ D₂
  l46_one : ∀ P D₁ D₂ : Subgroup G, IsSylowOf 2 P ⊤ → GomiE' P D₁ D₂ →
    CFSG.Open.IsElemAbelian 2 D₁
  l46_two : ∀ P D₁ D₂ Q₁ : Subgroup G, IsSylowOf 2 P ⊤ → GomiE' P D₁ D₂ → IsOtherSylow P D₁ Q₁ →
    D₁ = omegaOneCenterIn Q₁ ⊔ omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G))
  l46_sup : ∀ P D₁ D₂ : Subgroup G, IsSylowOf 2 P ⊤ → GomiE' P D₁ D₂ →
    D₁ ⊔ D₂ = P ⊓ Subgroup.normalizer (D₁ : Set G)
  l46_index : ∀ P D₁ D₂ Q₁ : Subgroup G, IsSylowOf 2 P ⊤ → GomiE' P D₁ D₂ →
    IsOtherSylow P D₁ Q₁ →
    (omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G)) ⊓ omegaOneCenterIn Q₁).relIndex
      (omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G))) =
      D₁.relIndex (P ⊓ Subgroup.normalizer (D₁ : Set G))

namespace ClassTwoSetup

variable [Finite G] {L M T : Subgroup G} {n : ℕ} (hc : ClassTwoSetup G L M T n)
include hc

theorem not_isSolvable : ¬ Group.IsSolvable G := by
  intro _
  exact hc.natBlock.not_isSolvable (Group.isSolvable_of_isSolvable_injective L.subtype_injective)

theorem oddCore_eq_bot : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥ := by
  intro N hN hodd
  rcases hc.sec4.hyp.simple.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    rw [h, Subgroup.card_top] at hodd
    have : Group.IsSolvable G := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    exact hc.not_isSolvable this

theorem pCore_eq_bot : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥ := by
  intro N hN h2
  rcases hc.sec4.hyp.simple.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    rw [h] at h2
    have hG : IsPGroup 2 G := h2.of_equiv Subgroup.topEquiv
    have : Group.IsNilpotent G := hG.isNilpotent
    exact hc.not_isSolvable inferInstance

theorem classLETwo_of_isPGroup {A : Subgroup G} (hA : IsPGroup 2 A) : ClassLETwo A := by
  obtain ⟨S, hS, hAS⟩ := exists_isSylowOf_ge (le_top : A ≤ ⊤) hA
  obtain ⟨g, -, hg⟩ := exists_eq_map_conj_of_isSylowOf hc.sec4.sylowG hS
  rw [hg] at hAS
  exact classLETwo_of_le (classLETwo_map_conj hc.class2 g) hAS

theorem mul_self_of_mem_zc (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) {S : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) : ∀ z ∈ S ⊓ Subgroup.centralizer (S : Set G), z * z = 1 := by
  obtain ⟨g, -, hg⟩ := exists_eq_map_conj_of_isSylowOf hc.sec4.sylowG hS
  rintro z ⟨hzS, hzc⟩
  rw [hg] at hzS hzc
  obtain ⟨t, ht, rfl⟩ := hzS
  have htZ : t ∈ ZT T := by
    refine mem_ZT.2 ⟨ht, fun t' ht' => ?_⟩
    have h1 := Subgroup.mem_centralizer_iff.1 hzc ((MulAut.conj g).toMonoidHom t')
      ⟨t', ht', rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    have e : g * (t' * t) * g⁻¹ = g * (t * t') * g⁻¹ := by
      calc g * (t' * t) * g⁻¹ = (g * t' * g⁻¹) * (g * t * g⁻¹) := by group
        _ = (g * t * g⁻¹) * (g * t' * g⁻¹) := h1
        _ = g * (t * t') * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)
  have h2 := hc.elem_ZT hWVE t htZ
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
    _ = 1 := by rw [h2]; group

theorem gomiAmbient (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) : GomiAmbient G :=
  ⟨hc.sec4.hyp.charTwo, fun _ _ _ _ hS => hc.classLETwo_of_isPGroup hS.isPGroup,
    fun _ hS _ => hc.mul_self_of_mem_zc hWVE hS⟩

theorem exists_gomiE (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T)
    {P D₁ : Subgroup G} (hP : IsSylowOf 2 P ⊤) (hD₁ : GomiD P D₁) :
    ∃ D₂ : Subgroup G, GomiE P D₁ D₂ := by
  have hA := hc.gomiAmbient hWVE
  exact _root_.CFSG.CGT.PushingUpLit.C2L.exists_gomiE hc.oddCore_eq_bot hc.pCore_eq_bot
    hA.charTwo (fun _ hH S hS => hA.classTwo _ hH.isTwoLocal hH.not_twoClosed S hS)
    (fun S hS hcl z hz hzc => hA.zElem S hS hcl z ⟨hz, Subgroup.mem_centralizer_iff.2 hzc⟩)
    hP hD₁

theorem gomiD_Dc (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T)
    (h46 : Gomi46Data G) : GomiD T (Dc L T) := by
  have hA := hc.gomiAmbient hWVE
  have hTG := hc.sec4.sylowG
  obtain ⟨D₁, hDD₁, hD₁⟩ := exists_maximal_ge_of_wellFoundedGT (GomiHIn T) (Dc L T) hc.gomiHIn_Dc
  obtain ⟨D₂, hE⟩ := hc.exists_gomiE hWVE hTG hD₁
  have hE' : GomiE' T D₁ D₂ := h46.l47 T D₁ D₂ hTG hE
  have hel : CFSG.Open.IsElemAbelian 2 D₁ := h46.l46_one T D₁ D₂ hTG hE'
  have hle : D₁ ≤ Dc L T := fun x hx =>
    hc.gomiH_Dc.centralizer_le hA.charTwo (Subgroup.mem_centralizer_iff.2 fun y hy =>
      congrArg Subtype.val (hel.1.is_comm.comm ⟨y, hDD₁ hy⟩ ⟨x, hx⟩))
  exact (le_antisymm hle hDD₁) ▸ hD₁

end ClassTwoSetup

theorem card_eq_of_sup_relIndex [Finite G] {D X X₁ : Subgroup G} (hD : D = X₁ ⊔ X)
    (hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hcard : Nat.card X₁ = Nat.card X) {k : ℕ}
    (hk : (X ⊓ X₁).relIndex X = k) :
    Nat.card D = k * Nat.card X := by
  have hXD : X ≤ D := hD ▸ le_sup_right
  have hX₁D : X₁ ≤ D := hD ▸ le_sup_left
  have hn : X ≤ Subgroup.normalizer (X₁ : Set G) := fun x hx =>
    Subgroup.mem_normalizer_fintype fun z hz => by
      have := hcomm x (hXD hx) z (hX₁D hz)
      rw [this]
      simpa using hz
  have hprod := card_sup_mul_card_inf_of_le_normalizer hn
  rw [← hD, inf_comm, hcard] at hprod
  have h1 : k * Nat.card ↥(X ⊓ X₁) = Nat.card X := by
    have := Subgroup.relIndex_mul_card (H := X ⊓ X₁) (K := X)
    rwa [inf_of_le_left (inf_le_left : X ⊓ X₁ ≤ X), hk] at this
  have hz : 0 < Nat.card ↥(X ⊓ X₁) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hz
  calc Nat.card D * Nat.card ↥(X ⊓ X₁) = Nat.card X * Nat.card X := hprod
    _ = Nat.card X * (k * Nat.card ↥(X ⊓ X₁)) := by rw [h1]
    _ = k * Nat.card X * Nat.card ↥(X ⊓ X₁) := by ring

end CFSG.CGT.PushingUpLit.C2L
