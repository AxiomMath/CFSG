module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Gen
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator

section Action

variable {X : Type} [Group X]

@[expose] noncomputable def actHom (K : Subgroup X) :
    ↥(Subgroup.normalizer (K : Set X)) →* MulAut (↥K ⧸ Subgroup.center ↥K) :=
  i271Act K (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K))

theorem actHom_mk (K : Subgroup X) (n : ↥(Subgroup.normalizer (K : Set X))) (k : ↥K) :
    actHom K n (QuotientGroup.mk k) =
      (QuotientGroup.mk (K.normalizerMonoidHom n k) : ↥K ⧸ Subgroup.center ↥K) := rfl

theorem coe_normalizerMonoidHom (K : Subgroup X) (n : ↥(Subgroup.normalizer (K : Set X)))
    (k : ↥K) : (K.normalizerMonoidHom n k : X) = (n : X) * (k : X) * (n : X)⁻¹ := rfl

@[expose] def centreOf (K : Subgroup X) : Subgroup X := (Subgroup.center ↥K).map K.subtype

theorem mem_centreOf {K : Subgroup X} {z : X} :
    z ∈ centreOf K ↔ ∃ h : z ∈ K, (⟨z, h⟩ : ↥K) ∈ Subgroup.center ↥K := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, hw⟩
  · rintro ⟨h, hz⟩
    exact ⟨⟨z, h⟩, hz, rfl⟩

theorem centreOf_le (K : Subgroup X) : centreOf K ≤ K := by
  rintro _ ⟨w, -, rfl⟩
  exact w.2

theorem mem_centralizer_of_mem_centreOf {K : Subgroup X} {z : X} (hz : z ∈ centreOf K) :
    z ∈ Subgroup.centralizer (K : Set X) := by
  obtain ⟨h, hz⟩ := mem_centreOf.1 hz
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg (fun w : ↥K => (w : X)) (Subgroup.mem_center_iff.1 hz ⟨y, hy⟩)

theorem comm_mem_centreOf_of_fixed (K : Subgroup X) {b : X}
    (hb : b ∈ Subgroup.normalizer (K : Set X)) (k : ↥K)
    (hfix : actHom K ⟨b, hb⟩ (QuotientGroup.mk k) = QuotientGroup.mk k) :
    (k : X) * b * (k : X)⁻¹ * b⁻¹ ∈ centreOf K := by
  rw [actHom_mk] at hfix
  have h1 := QuotientGroup.eq.1 hfix
  set w : ↥K := (K.normalizerMonoidHom ⟨b, hb⟩ k)⁻¹ * k with hwdef
  have hw : (w : X) = b * (k : X)⁻¹ * b⁻¹ * k := by
    rw [hwdef]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_normalizerMonoidHom]
    group
  have hc : (k : X) * (w : X) = (w : X) * (k : X) :=
    congrArg (fun w : ↥K => (w : X)) (Subgroup.mem_center_iff.1 h1 k)
  refine ⟨w, h1, ?_⟩
  show (w : X) = _
  calc (w : X) = ((w : X) * (k : X)) * (k : X)⁻¹ := by group
    _ = ((k : X) * (w : X)) * (k : X)⁻¹ := by rw [hc]
    _ = (k : X) * (b * (k : X)⁻¹ * b⁻¹ * k) * (k : X)⁻¹ := by rw [hw]
    _ = (k : X) * b * (k : X)⁻¹ * b⁻¹ := by group

end Action

section Pre

variable {X : Type} [Group X]

@[expose] noncomputable def actPre (B K : Subgroup X)
    (P : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))) : Subgroup X :=
  (((B ⊓ Subgroup.normalizer (K : Set X)).subgroupOf (Subgroup.normalizer (K : Set X))) ⊓
    P.comap (actHom K)).map (Subgroup.normalizer (K : Set X)).subtype

@[expose] noncomputable def autImage (B K : Subgroup X) :
    Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K)) :=
  ((B ⊓ Subgroup.normalizer (K : Set X)).subgroupOf (Subgroup.normalizer (K : Set X))).map
    (actHom K)

theorem mem_actPre {B K : Subgroup X} {P : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))}
    {x : X} : x ∈ actPre B K P ↔
      ∃ hx : x ∈ Subgroup.normalizer (K : Set X), x ∈ B ∧ actHom K ⟨x, hx⟩ ∈ P := by
  constructor
  · rintro ⟨n, ⟨hnB, hnP⟩, rfl⟩
    exact ⟨n.2, (Subgroup.mem_subgroupOf.1 hnB).1, hnP⟩
  · rintro ⟨hx, hxB, hxP⟩
    exact ⟨⟨x, hx⟩, ⟨Subgroup.mem_subgroupOf.2 ⟨hxB, hx⟩, hxP⟩, rfl⟩

theorem mem_autImage {B K : Subgroup X} {e : MulAut (↥K ⧸ Subgroup.center ↥K)} :
    e ∈ autImage B K ↔
      ∃ (x : X) (hx : x ∈ Subgroup.normalizer (K : Set X)), x ∈ B ∧ actHom K ⟨x, hx⟩ = e := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, n.2, (Subgroup.mem_subgroupOf.1 hn).1, rfl⟩
  · rintro ⟨x, hx, hxB, rfl⟩
    exact ⟨⟨x, hx⟩, Subgroup.mem_subgroupOf.2 ⟨hxB, hx⟩, rfl⟩

theorem actPre_le_left {B K : Subgroup X} {P : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))} :
    actPre B K P ≤ B := fun _ hx => (mem_actPre.1 hx).choose_spec.1

theorem actHom_eq_one_of_mem_centralizer (K : Subgroup X) {c : X}
    (hc : c ∈ Subgroup.centralizer (K : Set X)) :
    actHom K ⟨c, Subgroup.centralizer_le_normalizer (K : Set X) hc⟩ = 1 := by
  ext s
  induction s using QuotientGroup.induction_on with
  | H k =>
    rw [actHom_mk]
    show (QuotientGroup.mk (K.normalizerMonoidHom _ k) : ↥K ⧸ Subgroup.center ↥K) = _
    congr 1
    apply Subtype.ext
    rw [coe_normalizerMonoidHom]
    have := Subgroup.mem_centralizer_iff.1 hc (k : X) k.2
    show c * (k : X) * c⁻¹ = (k : X)
    rw [← this]
    group

theorem centralizer_inf_le_actPre (B K : Subgroup X)
    (P : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))) :
    B ⊓ Subgroup.centralizer (K : Set X) ≤ actPre B K P := by
  rintro c ⟨hcB, hcK⟩
  refine mem_actPre.2 ⟨Subgroup.centralizer_le_normalizer (K : Set X) hcK, hcB, ?_⟩
  rw [actHom_eq_one_of_mem_centralizer K hcK]
  exact P.one_mem

theorem isElemAbelian_actPre {p : ℕ} {B K : Subgroup X}
    (P : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))) (hB : IsElemAbelian p B) :
    IsElemAbelian p (actPre B K P) :=
  CFSG.Open.IsElemAbelian.mono hB actPre_le_left

end Pre

section Lift

variable {X : Type} [Group X]

@[expose] def CenterLift (B K : Subgroup X) : Prop :=
  ∀ b ∈ B, ∀ k ∈ K, k * b * k⁻¹ * b⁻¹ ∈ centreOf K → k * b * k⁻¹ * b⁻¹ ∈ B

theorem conj_mem_actPre {B K : Subgroup X} {P : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))}
    (hlift : CenterLift B K) {k : ↥K}
    (hk : ∀ e ∈ P, e (QuotientGroup.mk k) = QuotientGroup.mk k) {q : X} (hq : q ∈ actPre B K P) :
    (k : X) * q * (k : X)⁻¹ ∈ actPre B K P := by
  obtain ⟨hqN, hqB, hqP⟩ := mem_actPre.1 hq
  have hfix := hk _ hqP
  have hw := comm_mem_centreOf_of_fixed K hqN k hfix
  have hwB := hlift q hqB k k.2 hw
  have hwC : (k : X) * q * (k : X)⁻¹ * q⁻¹ ∈ B ⊓ Subgroup.centralizer (K : Set X) :=
    ⟨hwB, mem_centralizer_of_mem_centreOf hw⟩
  have hwP := centralizer_inf_le_actPre B K P hwC
  have : (k : X) * q * (k : X)⁻¹ = ((k : X) * q * (k : X)⁻¹ * q⁻¹) * q := by group
  rw [this]
  exact (actPre B K P).mul_mem hwP hq

theorem mem_normalizer_actPre {B K : Subgroup X}
    {P : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))} (hlift : CenterLift B K) {k : ↥K}
    (hk : ∀ e ∈ P, e (QuotientGroup.mk k) = QuotientGroup.mk k) :
    (k : X) ∈ Subgroup.normalizer (actPre B K P : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact conj_mem_actPre hlift hk hh
  · intro hh
    have hk' : ∀ e ∈ P, e (QuotientGroup.mk k⁻¹) = QuotientGroup.mk k⁻¹ := by
      intro e he
      rw [QuotientGroup.mk_inv, map_inv, hk e he]
    have := conj_mem_actPre hlift hk' hh
    have e : ((k⁻¹ : ↥K) : X) * ((k : X) * h * (k : X)⁻¹) * ((k⁻¹ : ↥K) : X)⁻¹ = h := by
      simp only [Subgroup.coe_inv, inv_inv]
      group
    rwa [e] at this

theorem card_actPre {B K : Subgroup X} (hperf : commutator ↥K = ⊤)
    {P : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))} (hP : P ≤ autImage B K) :
    Nat.card (actPre B K P) =
      Nat.card (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) * Nat.card P := by
  set N := Subgroup.normalizer (K : Set X) with hN
  set θ := actHom K with hθ
  set A' : Subgroup ↥N := (B ⊓ N).subgroupOf N with hA'
  set Q' : Subgroup ↥N := A' ⊓ P.comap θ with hQ'
  have hker : θ.ker = (Subgroup.centralizer (K : Set X)).subgroupOf N :=
    ker_i271Act hperf (MulEquiv.refl (↥K ⧸ Subgroup.center ↥K))
  have h1 : Nat.card (actPre B K P) = Nat.card Q' :=
    Subgroup.card_map_of_injective N.subtype_injective
  have h2 : θ.ker.relIndex Q' * Nat.card (θ.ker ⊓ Q' : Subgroup ↥N) = Nat.card Q' :=
    Subgroup.relIndex_mul_card θ.ker Q'
  have h3 : θ.ker.relIndex Q' = Nat.card (Q'.map θ) := Subgroup.relIndex_ker Q' θ
  have h4 : Q'.map θ = P := by
    apply le_antisymm
    · rintro _ ⟨a, ⟨-, ha⟩, rfl⟩
      exact ha
    · intro e he
      obtain ⟨a, ha, hae⟩ := hP he
      refine ⟨a, ⟨ha, ?_⟩, hae⟩
      show θ a ∈ P
      rw [hae]
      exact he
  have h5 : θ.ker ⊓ Q' = θ.ker ⊓ A' := by
    apply le_antisymm
    · exact inf_le_inf_left _ inf_le_left
    · intro a ha
      refine ⟨ha.1, ha.2, ?_⟩
      show θ a ∈ P
      rw [MonoidHom.mem_ker.1 ha.1]
      exact P.one_mem
  have h6 : Nat.card (θ.ker ⊓ A' : Subgroup ↥N) =
      Nat.card (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) := by
    have : (θ.ker ⊓ A').map N.subtype = B ⊓ Subgroup.centralizer (K : Set X) := by
      ext x
      constructor
      · rintro ⟨a, ⟨hk, ha⟩, rfl⟩
        refine ⟨(Subgroup.mem_subgroupOf.1 ha).1, ?_⟩
        have hk' : a ∈ (Subgroup.centralizer (K : Set X)).subgroupOf N := hker ▸ hk
        exact Subgroup.mem_subgroupOf.1 hk'
      · rintro ⟨hxB, hxK⟩
        have hxN : x ∈ N := Subgroup.centralizer_le_normalizer _ hxK
        refine ⟨⟨x, hxN⟩, ⟨?_, Subgroup.mem_subgroupOf.2 ⟨hxB, hxN⟩⟩, rfl⟩
        rw [hker]
        exact Subgroup.mem_subgroupOf.2 hxK
    rw [← this]
    exact (Subgroup.card_map_of_injective N.subtype_injective).symm
  rw [h1, ← h2, h3, h4, h5, h6, mul_comm]

end Lift

end CFSG.HardMathSupport.Dickson.I271
