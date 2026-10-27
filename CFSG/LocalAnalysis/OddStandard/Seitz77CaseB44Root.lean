module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44Diag
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44Basic

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.OddStandard.Seitz77.CaseB45
  CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open scoped commutatorElement

section Yof

variable {G : Type} [Group G] {A₁ B₁ : Subgroup G} {t : G}

theorem SwapPair.dg_mul (P : SwapPair A₁ B₁ t) {a b : G} (ha : a ∈ A₁) (hb : b ∈ A₁) :
    (a * b) * (t * (a * b) * t⁻¹) = (a * (t * a * t⁻¹)) * (b * (t * b * t⁻¹)) := by
  have h := P.comm b hb (t * a * t⁻¹) (P.swap₁ a ha)
  calc (a * b) * (t * (a * b) * t⁻¹) = a * (b * (t * a * t⁻¹)) * (t * b * t⁻¹) := by group
    _ = a * ((t * a * t⁻¹) * b) * (t * b * t⁻¹) := by rw [h]
    _ = (a * (t * a * t⁻¹)) * (b * (t * b * t⁻¹)) := by group

@[expose] def dgA (P : SwapPair A₁ B₁ t) : ↥A₁ →* G where
  toFun a := (a : G) * (t * (a : G) * t⁻¹)
  map_one' := by simp
  map_mul' a b := P.dg_mul a.2 b.2

theorem SwapPair.dg_eq_one (P : SwapPair A₁ B₁ t) {a : G} (ha : a ∈ A₁)
    (h : a * (t * a * t⁻¹) = 1) : a = 1 :=
  (P.unique ha A₁.one_mem (P.swap₁ a ha) B₁.one_mem (by rw [h, mul_one])).1

theorem SwapPair.dgA_injective (P : SwapPair A₁ B₁ t) : Function.Injective (dgA P) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  exact Subtype.ext (P.dg_eq_one a.2 ha)

theorem SwapPair.dg_comm_t (P : SwapPair A₁ B₁ t) {a : G} (ha : a ∈ A₁) :
    (a * (t * a * t⁻¹)) * t = t * (a * (t * a * t⁻¹)) := by
  have h1 : t * (a * (t * a * t⁻¹)) * t⁻¹ = (t * a * t⁻¹) * a := by
    calc t * (a * (t * a * t⁻¹)) * t⁻¹ = (t * a * t⁻¹) * (t * (t * a * t⁻¹) * t⁻¹) := by group
      _ = (t * a * t⁻¹) * a := by rw [P.conj_conj]
  have h2 : (t * a * t⁻¹) * a = a * (t * a * t⁻¹) := (P.comm a ha _ (P.swap₁ a ha)).symm
  calc (a * (t * a * t⁻¹)) * t = (t * (a * (t * a * t⁻¹)) * t⁻¹) * t := by rw [h1, h2]
    _ = t * (a * (t * a * t⁻¹)) := by group

@[expose] def Yof (P : SwapPair A₁ B₁ t) (U : Subgroup G) : Subgroup G :=
  (U.comap (dgA P)).map A₁.subtype

theorem mem_Yof (P : SwapPair A₁ B₁ t) {U : Subgroup G} {y : G} :
    y ∈ Yof P U ↔ y ∈ A₁ ∧ y * (t * y * t⁻¹) ∈ U := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, ha⟩
  · rintro ⟨hy, hU⟩
    exact ⟨⟨y, hy⟩, hU, rfl⟩

theorem Yof_le (P : SwapPair A₁ B₁ t) {U : Subgroup G} : Yof P U ≤ A₁ := fun _ hy =>
  ((mem_Yof P).mp hy).1

theorem Yof_comm (P : SwapPair A₁ B₁ t) {V U : Subgroup G}
    (hVd : ∀ a ∈ A₁, a * (t * a * t⁻¹) ∈ V) (hUc : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) :
    ∀ y ∈ Yof P U, ∀ a ∈ A₁, y * a = a * y := by
  intro y hy a ha
  obtain ⟨hyA, hyU⟩ := (mem_Yof P).mp hy
  have h1 := hUc _ hyU _ (hVd a ha)
  have h2 : (y * a) * (t * (y * a) * t⁻¹) = (a * y) * (t * (a * y) * t⁻¹) := by
    rw [P.dg_mul hyA ha, P.dg_mul ha hyA]
    exact h1
  have := P.dgA_injective (a₁ := ⟨y * a, A₁.mul_mem hyA ha⟩) (a₂ := ⟨a * y, A₁.mul_mem ha hyA⟩) h2
  exact congrArg Subtype.val this

theorem Yof_not_comm (P : SwapPair A₁ B₁ t) {V U : Subgroup G}
    (hV : ∀ v ∈ V, ∃ a ∈ A₁, v = a * (t * a * t⁻¹)) (hUV : U ≤ V)
    (hne : ∃ u ∈ U, ∃ v ∈ V, u * v ≠ v * u) :
    ¬ ∀ y ∈ Yof P U, ∀ a ∈ A₁, y * a = a * y := by
  intro hall
  obtain ⟨u, hu, v, hv, huv⟩ := hne
  obtain ⟨y, hy, rfl⟩ := hV u (hUV hu)
  obtain ⟨a, ha, rfl⟩ := hV v hv
  have hyY : y ∈ Yof P U := (mem_Yof P).mpr ⟨hy, hu⟩
  apply huv
  rw [← P.dg_mul hy ha, ← P.dg_mul ha hy, hall y hyY a ha]

theorem Yof_card (P : SwapPair A₁ B₁ t) {V U : Subgroup G}
    (hV : ∀ v ∈ V, ∃ a ∈ A₁, v = a * (t * a * t⁻¹)) (hUV : U ≤ V) :
    Nat.card ↥(Yof P U) = Nat.card ↥U := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun y : ↥(Yof P U) => (⟨(y : G) * (t * (y : G) * t⁻¹), ((mem_Yof P).mp y.2).2⟩ : ↥U))
    ⟨?_, ?_⟩)
  · intro y y' h
    have h' : (y : G) * (t * (y : G) * t⁻¹) = (y' : G) * (t * (y' : G) * t⁻¹) :=
      congrArg Subtype.val h
    have hA := ((mem_Yof P).mp y.2).1
    have hA' := ((mem_Yof P).mp y'.2).1
    have := P.dgA_injective (a₁ := ⟨y, hA⟩) (a₂ := ⟨y', hA'⟩) h'
    exact Subtype.ext (Subtype.mk.inj this)
  · intro u
    obtain ⟨a, ha, hau⟩ := hV u (hUV u.2)
    exact ⟨⟨a, (mem_Yof P).mpr ⟨ha, hau ▸ u.2⟩⟩, Subtype.ext hau.symm⟩

end Yof

section Side

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {t : G} {c : CaseB A R t}
  {M M' S A₁ B₁ : Subgroup G}

structure Side (c : CaseB A R t) (M M' S A₁ B₁ : Subgroup G) : Prop where
  F : c.Factors M M'
  hZ : c.OddCoreCentral
  P : SwapPair A₁ B₁ t
  S_eq : S = A₁ ⊔ B₁
  A_eq : S ⊓ M = A₁
  B_eq : S ⊓ M' = B₁
  W_le : c.W ≤ S
  S_sylow : IsSylowOf 2 S c.Ninf

variable (Sd : Side c M M' S A₁ B₁)

include Sd

theorem Side.A₁_le : A₁ ≤ M := Sd.A_eq ▸ inf_le_right

theorem Side.W_inf_le : c.W ⊓ M ≤ A₁ := fun x hx => by
  rw [← Sd.A_eq]
  exact ⟨Sd.W_le hx.1, hx.2⟩

theorem Side.W_inf_le' : c.W ⊓ M' ≤ B₁ := fun x hx => by
  rw [← Sd.B_eq]
  exact ⟨Sd.W_le hx.1, hx.2⟩

theorem Side.sylow : IsSylowOf 2 A₁ M := by
  have hO : Odd2 M M' :=
    ⟨fun x hx m hm => Sd.F.norm₁ x (Sd.F.ninf_eq ▸ hx) m hm,
      fun x hx m hm => Sd.F.norm₂ x (Sd.F.ninf_eq ▸ hx) m hm, Sd.F.odd_inf⟩
  have hSn : IsSylowOf 2 S (M ⊔ M') := Sd.F.ninf_eq ▸ Sd.S_sylow
  have := (hO.sylow_inf hSn).1
  rwa [Sd.A_eq] at this

theorem Side.mem_W_of_diag {a : G} (ha : a ∈ A₁) (h : a * (t * a * t⁻¹) ∈ c.W) : a ∈ c.W := by
  have h' : a * (t * a * t⁻¹) ∈ (c.W ⊓ M) ⊔ (c.W ⊓ M') := by rw [Sd.F.W_eq]; exact h
  obtain ⟨w₁, hw₁, w₂, hw₂, hw⟩ := mem_sup_of_forall_comm (O := c.W ⊓ M) (E := c.W ⊓ M')
    (fun x hx y hy => comm_of_isElemAbelian_two c.W_elem hx.1 hy.1) h'
  have := Sd.P.unique ha (Sd.W_inf_le hw₁) (Sd.P.swap₁ a ha) (Sd.W_inf_le' hw₂) hw
  rw [this.1]
  exact hw₁.1

theorem Side.dg_conj {m y : G} (hm : m ∈ M) (hy : y ∈ M) :
    (m * (t * m * t⁻¹)) * (y * (t * y * t⁻¹)) * (m * (t * m * t⁻¹))⁻¹ =
      (m * y * m⁻¹) * (t * (m * y * m⁻¹) * t⁻¹) := by
  have hmym : m * y * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm hy) (M.inv_mem hm)
  have h1 := Sd.F.diag_mul Sd.hZ hm hy
  have h2 := Sd.F.diag_mul Sd.hZ hmym hm
  have e : m * y * m⁻¹ * m = m * y := by group
  rw [e] at h2
  rw [mul_inv_eq_iff_eq_mul]
  calc (m * (t * m * t⁻¹)) * (y * (t * y * t⁻¹)) = (m * y) * (t * (m * y) * t⁻¹) := h1.symm
    _ = ((m * y * m⁻¹) * (t * (m * y * m⁻¹) * t⁻¹)) * (m * (t * m * t⁻¹)) := h2

theorem Side.dg_inv {m : G} (hm : m ∈ M) :
    (m * (t * m * t⁻¹))⁻¹ = m⁻¹ * (t * m⁻¹ * t⁻¹) := by
  have hcomm : Commute m (t * m * t⁻¹) := Sd.F.comm_elem Sd.hZ hm (Sd.F.swap₁ m hm)
  have e : t * m⁻¹ * t⁻¹ = (t * m * t⁻¹)⁻¹ := by group
  rw [e, mul_inv_rev]
  exact hcomm.inv_inv.eq.symm

theorem Side.dg_conj_self {m y : G} (hm : m ∈ M) (hy : y ∈ M) :
    (m * (t * m * t⁻¹)) * y * (m * (t * m * t⁻¹))⁻¹ = m * y * m⁻¹ := Sd.F.diag_conj Sd.hZ hm hy

theorem Side.cs_Yof_le {m : G} (hm : m ∈ M) {U U' : Subgroup G} (hU : U ≤ c.W)
    (h : ∀ x ∈ U, (m * (t * m * t⁻¹)) * x * (m * (t * m * t⁻¹))⁻¹ ∈ U') :
    cs m (Yof Sd.P U) ≤ Yof Sd.P U' := by
  intro z hz
  rw [mem_cs] at hz
  obtain ⟨hyA, hyU⟩ := (mem_Yof Sd.P).mp hz
  have hyW : m⁻¹ * z * m ∈ c.W := Sd.mem_W_of_diag hyA (hU hyU)
  have hyM : m⁻¹ * z * m ∈ M := Sd.A₁_le hyA
  have hmN : m ∈ c.N := prOf_le c.N (Sd.F.M₁_le hm)
  have hmyW : m * (m⁻¹ * z * m) * m⁻¹ ∈ c.W ⊓ M :=
    ⟨(mem_normalizer_iff.mp hmN _).mp hyW, M.mul_mem (M.mul_mem hm hyM) (M.inv_mem hm)⟩
  have hz' : m * (m⁻¹ * z * m) * m⁻¹ = z := by group
  rw [hz'] at hmyW
  refine (mem_Yof Sd.P).mpr ⟨Sd.W_inf_le hmyW, ?_⟩
  have := h _ hyU
  rw [Sd.dg_conj hm hyM, hz'] at this
  exact this

theorem Side.cs_Yof {m : G} (hm : m ∈ M) {U U' : Subgroup G} (hU : U ≤ c.W) (hU' : U' ≤ c.W)
    (hcs : cs (m * (t * m * t⁻¹)) U = U') : cs m (Yof Sd.P U) = Yof Sd.P U' := by
  refine le_antisymm (Sd.cs_Yof_le hm hU fun x hx => ?_) ?_
  · rw [← hcs]
    exact mem_cs_iff.mpr hx
  · have hm' : m⁻¹ ∈ M := M.inv_mem hm
    have h := Sd.cs_Yof_le hm' hU' (U' := U) (fun x hx => ?_)
    · calc Yof Sd.P U' = cs m (cs m⁻¹ (Yof Sd.P U')) := (cs_cs_inv _ _).symm
        _ ≤ cs m (Yof Sd.P U) := cs_mono m h
    · have hx' : x ∈ cs (m * (t * m * t⁻¹)) U := hcs ▸ hx
      rw [mem_cs] at hx'
      have e : (m⁻¹ * (t * m⁻¹ * t⁻¹)) * x * (m⁻¹ * (t * m⁻¹ * t⁻¹))⁻¹ =
          (m * (t * m * t⁻¹))⁻¹ * x * (m * (t * m * t⁻¹)) := by
        rw [← Sd.dg_inv hm]
        group
      rw [e]
      exact hx'

theorem Side.Yof_inf_W {U : Subgroup G} (hUR : U ⊓ R = ⊥) : Yof Sd.P U ⊓ c.W = ⊥ := by
  refine eq_bot_iff.mpr fun y hy => ?_
  obtain ⟨hyY, hyW⟩ := hy
  obtain ⟨hyA, hyU⟩ := (mem_Yof Sd.P).mp hyY
  have htW : t * y * t⁻¹ ∈ c.W := (mem_normalizer_iff.mp c.t_mem_N y).mp hyW
  have hdW : y * (t * y * t⁻¹) ∈ c.W := c.W.mul_mem hyW htW
  have hdC : y * (t * y * t⁻¹) ∈ centralizer ({t} : Set G) :=
    mem_centralizer_singleton_iff.mpr (Sd.P.dg_comm_t hyA)
  have hdR : y * (t * y * t⁻¹) ∈ R := by
    rw [← c.W_inf_centralizer_t]
    exact ⟨hdW, hdC⟩
  have h1 : y * (t * y * t⁻¹) ∈ U ⊓ R := ⟨hyU, hdR⟩
  rw [hUR, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.mpr (Sd.P.dg_eq_one hyA h1)

end Side

theorem CaseB.center_le_centralizer_W {G : Type} [Group G] [Finite G] {A R : Subgroup G} {t : G}
    (c : CaseB A R t) : A ⊓ centralizer (A : Set G) ≤ centralizer (c.W : Set G) := by
  intro z hz
  have S := c.H.sit.S
  have hodd : Odd (orderOf z) := by
    have := orderOf_dvd_natCard (⟨z, hz⟩ : ↥(A ⊓ centralizer (A : Set G)))
    rw [Subgroup.orderOf_mk] at this
    exact S.odd_inf.of_dvd_nat this
  have hle : (R ⊔ zpowers t : Subgroup G) ≤ centralizer ({z} : Set G) := by
    refine sup_le (fun r hr => ?_) (zpowers_le.mpr ?_)
    · rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.mp hz.2 r (S.W_le_A hr)
    · rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.mp S.t_cent z hz.1).symm
  have hzE : z ∈ centralizer ((R ⊔ zpowers t : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro e he
    exact mem_centralizer_singleton_iff.mp (hle he)
  exact c.H.O_le_centralizer_W (S.mem_O_of_odd hzE hodd)

section CS

variable {G : Type} [Group G] [Finite G] {A V₁ V₂ : Subgroup G} {d : Datum A}
  {c₁ : CaseB A V₁ d.t} {c₂ : CaseB A V₂ d.t} {M₁ M₂ N₁ N₂ S A₁ B₁ : Subgroup G} {k : Type}
  [Field k] {e : ↥A₁ ≃* ↥(unipAll k)} (CS : CommonSylow c₁ c₂ M₁ M₂ N₁ N₂ S A₁ B₁ e)

include CS

theorem CommonSylow.side₁ (hZ₁ : c₁.OddCoreCentral) : Side c₁ M₁ M₂ S A₁ B₁ :=
  ⟨CS.F₁, hZ₁, CS.swapPair, CS.S_eq, CS.syl.A₁_eq.symm, CS.syl.B₁_eq.symm, CS.W₁_le_S,
    CS.syl.S₀_sylow⟩

theorem CommonSylow.side₂ (hZ₂ : c₂.OddCoreCentral) : Side c₂ N₁ N₂ S A₁ B₁ :=
  ⟨CS.F₂, hZ₂, CS.swapPair, CS.S_eq, CS.A_eq, CS.B_eq, CS.W₂_le_S, CS.S_sylow₂⟩

end CS

end CFSG.OddStandard.Seitz77
