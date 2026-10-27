module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseAClose2
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseACloseGal
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseAClose1

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools

section Close

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {F : Type} [Field F]
  [Finite F] [CharP F 2] {W S₁ S₀ W₀ : Subgroup G} {ι : G → F × F} {κ : G → F}
  {φ : G → RingAut F}

structure CloseData (S : SylowA d W S₁ S₀ W₀ ι κ φ) (T : Subgroup G) (ψ : ↥T →* RingAut F)
    (ε : ↥T →* Multiplicative (ZMod 2)) : Prop where
  isPGroup : IsPGroup 2 T
  not_two_dvd_index : ¬ 2 ∣ T.index
  S₁_le : S₁ ≤ T
  norm_S₀ : ∀ x ∈ T, ∀ s, s ∈ S₀ ↔ x * s * x⁻¹ ∈ S₀
  mem_S₀_iff : ∀ x : T, (x : G) ∈ S₀ ↔ ψ x = 1 ∧ ε x = 1
  ε_eq_one : ∀ x : T, (x : G) ∈ S₁ → ε x = 1
  ext : ∀ y : T, (y : G) * y = 1 → ψ y = 1 → ε y ≠ 1 →
    Nat.card ↥(S₀ ⊓ centralizer ({(y : G)} : Set G)) ≤ 16

@[expose] noncomputable def sqHom {T : Subgroup G} (ψ : ↥T →* RingAut F) : ↥T →* RingAut F :=
  MonoidHom.mk' (fun x => ψ x * ψ x) (fun x y => by
    simp only [map_mul]
    calc ψ x * ψ y * (ψ x * ψ y) = ψ x * (ψ y * ψ x) * ψ y := by group
      _ = ψ x * (ψ x * ψ y) * ψ y := by rw [ringAut_mul_comm (ψ y) (ψ x)]
      _ = ψ x * ψ x * (ψ y * ψ y) := by group)

theorem sqHom_apply {T : Subgroup G} (ψ : ↥T →* RingAut F) (x : T) :
    sqHom ψ x = ψ x * ψ x := rfl

namespace CloseData

variable {S : SylowA d W S₁ S₀ W₀ ι κ φ} {T : Subgroup G} {ψ : ↥T →* RingAut F}
  {ε : ↥T →* Multiplicative (ZMod 2)} (C : CloseData S T ψ ε)

include C

theorem t_mem : d.t ∈ T := C.S₁_le S.t_mem_S₁

@[expose] def tT : T := ⟨d.t, C.t_mem⟩

theorem ε_t : ε C.tT = 1 := C.ε_eq_one C.tT S.t_mem_S₁

theorem ψ_t_ne_one : ψ C.tT ≠ 1 := fun h =>
  S.t_not_mem_S₀ ((C.mem_S₀_iff C.tT).2 ⟨h, C.ε_t⟩)

theorem ψ_t_sq : ψ C.tT * ψ C.tT = 1 := by
  rw [← map_mul]
  have : C.tT * C.tT = 1 := Subtype.ext d.t_mul_self
  rw [this, map_one]

theorem mul_self_mem_iff (x : T) : (x : G) * x ∈ S₀ ↔ ψ x * ψ x = 1 := by
  have h := C.mem_S₀_iff (x * x)
  rw [map_mul, map_mul] at h
  have h2 : ε x * ε x = 1 := by
    generalize ε x = a
    revert a
    decide
  rw [h2] at h
  simpa using h

theorem comm_mem_S₀ (x y : T) : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ S₀ := by
  have h := (C.mem_S₀_iff (x * y * x⁻¹ * y⁻¹)).2 ⟨?_, ?_⟩
  · simpa using h
  · simp only [map_mul, map_inv]
    rw [ringAut_mul_comm (ψ x) (ψ y)]
    group
  · have key : ∀ a b : Multiplicative (ZMod 2), a * b * a⁻¹ * b⁻¹ = 1 := by decide
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact key _ _

end CloseData


theorem relIndex_map_subtype_eq_index {T : Subgroup G} (K : Subgroup ↥T) :
    (K.map T.subtype).relIndex T = K.index := by
  unfold Subgroup.relIndex
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective T.subtype_injective]

theorem index_ker_eq_two (hF : Nat.card F = 16) {T : Subgroup G} [Finite G]
    (ψ' : ↥T →* RingAut F) (h2 : ∀ x, ψ' x * ψ' x = 1) (h1 : ∃ x, ψ' x ≠ 1) :
    ψ'.ker.index = 2 := by
  have hle : Nat.card ψ'.range ≤ 2 := by
    have hsub : (ψ'.range : Set (RingAut F)) ⊆ {a : RingAut F | a * a = 1} := by
      rintro _ ⟨x, rfl⟩
      exact h2 x
    have hfin : Finite (RingAut F) := ringAut_finite
    calc Nat.card ψ'.range = (ψ'.range : Set (RingAut F)).ncard := (Nat.card_coe_set_eq _).symm
      _ ≤ Set.ncard {a : RingAut F | a * a = 1} := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := ringAut_card_sq_eq_one_le hF
  have hne1 : ψ'.ker.index ≠ 1 := by
    intro h
    rw [Subgroup.index_eq_one] at h
    obtain ⟨x, hx⟩ := h1
    exact hx (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x))
  have hne0 : ψ'.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have := Subgroup.index_ker ψ'
  omega

omit [Field F] [Finite F] [CharP F 2] in
theorem mem_map_subtype_ker_iff {T : Subgroup G} {M : Type*} [Group M] (θ : ↥T →* M) {g : G}
    (hg : g ∈ T) : g ∈ θ.ker.map T.subtype ↔ θ ⟨g, hg⟩ = 1 := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact MonoidHom.mem_ker.mp hz
  · intro h
    exact ⟨⟨g, hg⟩, MonoidHom.mem_ker.mpr h, rfl⟩

namespace CloseData

variable {S : SylowA d W S₁ S₀ W₀ ι κ φ} {T : Subgroup G} {ψ : ↥T →* RingAut F}
  {ε : ↥T →* Multiplicative (ZMod 2)} (C : CloseData S T ψ ε)

include C

theorem exists_sq_lift [Finite G] (h : Hyp G A) (x₀ : T)
    (hx₀ : ψ x₀ * ψ x₀ ≠ 1) :
    ∃ x₁ : T, ψ x₁ = ψ x₀ ∧ ((x₁ : G) * x₁) * ((x₁ : G) * x₁) = 1 ∧
      IsConj d.t ((x₁ : G) * x₁) := by
  have hsqeq : ψ x₀ * ψ x₀ = ψ C.tT :=
    ringAut_sq_eq_of_sq_ne_one S.card_F hx₀ C.ψ_t_sq C.ψ_t_ne_one
  have hsq : d.t⁻¹ * ((x₀ : G) * x₀) ∈ S₀ := by
    have h1 := (C.mem_S₀_iff (C.tT⁻¹ * (x₀ * x₀))).2 ⟨?_, ?_⟩
    · simpa [CloseData.tT] using h1
    · rw [map_mul, map_inv, map_mul, hsqeq]
      exact inv_mul_cancel _
    · rw [map_mul, map_inv, map_mul, C.ε_t]
      generalize ε x₀ = a
      revert a
      decide
  have hcomm : (x₀ : G) * d.t * (x₀ : G)⁻¹ * d.t⁻¹ ∈ S₀ := C.comm_mem_S₀ x₀ C.tT
  obtain ⟨x₁, hx₁S, hx₁sq, hx₁conj⟩ :=
    S.exists_involution_sq h (x₀ := (x₀ : G)) (C.norm_S₀ x₀ x₀.2) hcomm hsq
  have hk : (x₀ : G)⁻¹ * x₁ ∈ T := C.S₁_le (S.S₀_le_S₁ hx₁S)
  have hx₁T : x₁ ∈ T := by
    have : x₁ = (x₀ : G) * ((x₀ : G)⁻¹ * x₁) := by group
    rw [this]
    exact T.mul_mem x₀.2 hk
  refine ⟨⟨x₁, hx₁T⟩, ?_, hx₁sq, hx₁conj⟩
  have hx : (⟨x₁, hx₁T⟩ : T) = x₀ * ⟨(x₀ : G)⁻¹ * x₁, hk⟩ := Subtype.ext (by simp)
  have hker := ((C.mem_S₀_iff ⟨(x₀ : G)⁻¹ * x₁, hk⟩).1 hx₁S).1
  rw [hx, map_mul, hker, mul_one]


theorem false_of_exists_sq_ne_one [Finite G]
    (h : Hyp G A) (x₀ : T)
    (hx₀ : ψ x₀ * ψ x₀ ≠ 1) : False := by
  obtain ⟨x₁, hψ, hx₁sq, hx₁conj⟩ := C.exists_sq_lift h x₀ hx₀
  have : IsSimpleGroup G := h.simple
  let θ : ↥T →* RingAut F := sqHom ψ
  let M : Subgroup G := θ.ker.map T.subtype
  have hMT : M ≤ T := Subgroup.map_subtype_le _
  have hθ2 : ∀ x : T, θ x * θ x = 1 := fun x => by
    rw [sqHom_apply]
    calc ψ x * ψ x * (ψ x * ψ x) = ψ x ^ 4 := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := ringAut_pow_four S.card_F _
  have hMidx : M.relIndex T = 2 := by
    rw [relIndex_map_subtype_eq_index]
    exact index_ker_eq_two S.card_F θ hθ2 ⟨x₀, hx₀⟩
  have hmemM : ∀ g (hg : g ∈ T), g ∈ M ↔ ψ ⟨g, hg⟩ * ψ ⟨g, hg⟩ = 1 := fun g hg =>
    mem_map_subtype_ker_iff θ hg
  have hx₁M : (x₁ : G) ∉ M := by
    rw [hmemM _ x₁.2]
    exact hψ ▸ hx₀
  have hdM : ∀ y : G, y⁻¹ * ((x₁ : G) * x₁) * y ∈ T → y⁻¹ * ((x₁ : G) * x₁) * y ∈ M := by
    intro y hu
    rw [hmemM _ hu]
    have hu2 : (⟨_, hu⟩ : T) * ⟨_, hu⟩ = 1 := Subtype.ext (by
      show y⁻¹ * ((x₁ : G) * x₁) * y * (y⁻¹ * ((x₁ : G) * x₁) * y) = 1
      calc y⁻¹ * ((x₁ : G) * x₁) * y * (y⁻¹ * ((x₁ : G) * x₁) * y)
          = y⁻¹ * (((x₁ : G) * x₁) * ((x₁ : G) * x₁)) * y := by group
        _ = 1 := by rw [hx₁sq]; group)
    rw [← map_mul, hu2, map_one]
  obtain ⟨x, hxM, -⟩ :=
    CFSG.LargeExtraspecial.GLR.exists_extremal_conj_mem_of_sq_eq_of_isSimpleGroup h.nonab
      C.isPGroup C.not_two_dvd_index hMT hMidx x₁.2 hx₁M rfl hx₁sq hdM
  have hx₂T : x⁻¹ * (x₁ : G) * x ∈ T := hMT hxM
  have hx₂sq : ψ ⟨_, hx₂T⟩ * ψ ⟨_, hx₂T⟩ = 1 := (hmemM _ hx₂T).1 hxM
  have hx₂S := (C.mul_self_mem_iff ⟨_, hx₂T⟩).2 hx₂sq
  have heq : (x⁻¹ * (x₁ : G) * x) * (x⁻¹ * (x₁ : G) * x) = x⁻¹ * ((x₁ : G) * x₁) * x := by group
  have hx₂S' : x⁻¹ * ((x₁ : G) * x₁) * x ∈ S₀ := by
    rw [← heq]
    exact hx₂S
  have hinv : (x⁻¹ * ((x₁ : G) * x₁) * x) * (x⁻¹ * ((x₁ : G) * x₁) * x) = 1 := by
    calc (x⁻¹ * ((x₁ : G) * x₁) * x) * (x⁻¹ * ((x₁ : G) * x₁) * x)
        = x⁻¹ * (((x₁ : G) * x₁) * ((x₁ : G) * x₁)) * x := by group
      _ = 1 := by rw [hx₁sq]; group
  have hconj : IsConj d.t (x⁻¹ * ((x₁ : G) * x₁) * x) :=
    hx₁conj.trans (isConj_iff.mpr ⟨x⁻¹, by rw [inv_inv]⟩)
  exact S.not_conj_mem_S₀ h hx₂S' hinv hconj

end CloseData

theorem card_centralizer_conj (t x : G) :
    Nat.card ↥(centralizer ({x⁻¹ * t * x} : Set G)) = Nat.card ↥(centralizer ({t} : Set G)) := by
  have : centralizer ({x⁻¹ * t * x} : Set G) =
      (centralizer ({t} : Set G)).map (MulAut.conj x⁻¹).toMonoidHom := by
    ext z
    rw [mem_map_conj_iff, inv_inv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro hz
      calc x * z * x⁻¹ * t = x * (z * (x⁻¹ * t * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * t * x) * z) * x⁻¹ := by rw [hz]
        _ = t * (x * z * x⁻¹) := by group
    · intro hz
      calc z * (x⁻¹ * t * x) = x⁻¹ * (x * z * x⁻¹ * t) * x := by group
        _ = x⁻¹ * (t * (x * z * x⁻¹)) * x := by rw [hz]
        _ = x⁻¹ * t * x * z := by group
  rw [this, card_map_conj]

theorem card_P_ge [Finite G]
    (h : Hyp G A) (d : Datum A) :
    128 ≤ Nat.card d.P := by
  have hV := h.card_V d
  have hle : d.P ⊓ A ≤ d.P := inf_le_left
  have hdvd : 64 ∣ Nat.card d.P := hV ▸ Subgroup.card_dvd_of_le hle
  have hne : d.P ⊓ A ≠ d.P := fun heq => by
    have : d.t ∈ d.P ⊓ A := by rw [heq]; exact d.t_mem_P
    exact h.facts.t_not_mem_A d this.2
  have hlt : Nat.card d.P ≠ 64 := fun hc =>
    hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hV]))
  have hpos : 0 < Nat.card d.P := Nat.card_pos
  omega


namespace CloseData

variable {S : SylowA d W S₁ S₀ W₀ ι κ φ} {T : Subgroup G} {ψ : ↥T →* RingAut F}
  {ε : ↥T →* Multiplicative (ZMod 2)} (C : CloseData S T ψ ε)

include C

theorem false_of_sq_eq_one [Finite G]
    (h : Hyp G A)
    (hβ : ∀ x : T, ψ x * ψ x = 1) : False := by
  classical
  have : IsSimpleGroup G := h.simple
  let U₁ : Subgroup G := ψ.ker.map T.subtype
  have hU₁T : U₁ ≤ T := Subgroup.map_subtype_le _
  have hidx : U₁.relIndex T = 2 := by
    rw [relIndex_map_subtype_eq_index]
    exact index_ker_eq_two S.card_F ψ hβ ⟨C.tT, C.ψ_t_ne_one⟩
  have htU : d.t ∉ U₁ := fun hmem =>
    C.ψ_t_ne_one ((mem_map_subtype_ker_iff ψ C.t_mem).1 hmem)
  obtain ⟨x, hxU, hext⟩ :=
    CFSG.LargeExtraspecial.GLR.exists_extremal_conj_mem_of_sq_eq_of_isSimpleGroup h.nonab
      C.isPGroup C.not_two_dvd_index hU₁T hidx (g := d.t) (d := 1) C.t_mem htU d.t_mul_self
      (mul_one 1) (fun y _ => by simp)
  set y : G := x⁻¹ * d.t * x with hy
  have hyT : y ∈ T := hU₁T hxU
  have hyψ : ψ ⟨y, hyT⟩ = 1 := (mem_map_subtype_ker_iff ψ hyT).1 hxU
  have hy2 : y * y = 1 := by
    calc y * y = x⁻¹ * (d.t * d.t) * x := by rw [hy]; group
      _ = 1 := by rw [d.t_mul_self]; group
  have hyconj : IsConj d.t y := isConj_iff.mpr ⟨x⁻¹, by rw [hy, inv_inv]⟩
  have hyS : y ∉ S₀ := fun hmem => S.not_conj_mem_S₀ h hmem hy2 hyconj
  have hyε : ε ⟨y, hyT⟩ ≠ 1 := fun he => hyS ((C.mem_S₀_iff _).2 ⟨hyψ, he⟩)
  have hbound : Nat.card ↥(S₀ ⊓ centralizer ({y} : Set G)) ≤ 16 :=
    C.ext ⟨y, hyT⟩ hy2 hyψ hyε
  let Φ : G → RingAut F × Multiplicative (ZMod 2) := fun g =>
    if hg : g ∈ T then (ψ ⟨g, hg⟩, ε ⟨g, hg⟩) else 1
  have hΦdef : ∀ g (hg : g ∈ T), Φ g = (ψ ⟨g, hg⟩, ε ⟨g, hg⟩) := fun g hg => dite_eq_left hg
  have hΦ : ∀ a ∈ T ⊓ centralizer ({y} : Set G), ∀ b ∈ T ⊓ centralizer ({y} : Set G),
      Φ (a * b) = Φ a * Φ b := by
    intro a ha b hb
    have hab : a * b ∈ T := T.mul_mem ha.1 hb.1
    have e : (⟨a * b, hab⟩ : T) = ⟨a, ha.1⟩ * ⟨b, hb.1⟩ := rfl
    rw [hΦdef _ hab, hΦdef _ ha.1, hΦdef _ hb.1, e, map_mul, map_mul]
    rfl
  have hker : Nat.card {a : G // a ∈ T ⊓ centralizer ({y} : Set G) ∧ Φ a = 1} ≤ 16 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun a => (⟨a.1, ?_⟩ : ↥(S₀ ⊓ centralizer ({y} : Set G)))) ?_) hbound
    · obtain ⟨a, ha, hΦa⟩ := a
      rw [hΦdef a ha.1, Prod.mk_eq_one] at hΦa
      exact ⟨(C.mem_S₀_iff ⟨a, ha.1⟩).2 hΦa, ha.2⟩
    · intro a b hab
      have h1 := congrArg (fun z : ↥(S₀ ⊓ centralizer ({y} : Set G)) => (z : G)) hab
      exact Subtype.ext h1
  have him : (Φ '' ((T ⊓ centralizer ({y} : Set G) : Subgroup G) : Set G)).ncard ≤ 4 := by
    have hfin : Finite (RingAut F) := ringAut_finite
    have hsub : Φ '' ((T ⊓ centralizer ({y} : Set G) : Subgroup G) : Set G) ⊆
        {a : RingAut F | a * a = 1} ×ˢ (Set.univ : Set (Multiplicative (ZMod 2))) := by
      rintro _ ⟨a, ha, rfl⟩
      rw [hΦdef a ha.1]
      exact ⟨hβ _, Set.mem_univ _⟩
    calc (Φ '' ((T ⊓ centralizer ({y} : Set G) : Subgroup G) : Set G)).ncard
        ≤ ({a : RingAut F | a * a = 1} ×ˢ
            (Set.univ : Set (Multiplicative (ZMod 2)))).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = Set.ncard {a : RingAut F | a * a = 1} * 2 := by
          rw [Set.ncard_prod, Set.ncard_univ, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
      _ ≤ 2 * 2 := Nat.mul_le_mul (ringAut_card_sq_eq_one_le S.card_F) le_rfl
  have hK : Nat.card ↥(T ⊓ centralizer ({y} : Set G)) ≤ 16 * 4 :=
    card_le_mul_of_partial_hom _ Φ hΦ hker him
  have hsyl : IsSylowOf 2 (T ⊓ centralizer ({y} : Set G)) (centralizer ({y} : Set G)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isSylowOf_iff.2 hext
  have hcardK : Nat.card ↥(T ⊓ centralizer ({y} : Set G)) = Nat.card d.P := by
    rw [hsyl.card_eq, d.P_isSylow_centralizer.card_eq, hy, card_centralizer_conj]
  have := card_P_ge h d
  omega

theorem false [Finite G]
    (h : Hyp G A) : False := by
  by_cases hβ : ∀ x : T, ψ x * ψ x = 1
  · exact C.false_of_sq_eq_one h hβ
  · obtain ⟨x₀, hx₀⟩ := not_forall.mp hβ
    exact C.false_of_exists_sq_ne_one h x₀ hx₀

end CloseData

end Close

end CFSG.OddStandard.Seitz77
