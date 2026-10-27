module

public import CFSG.GH74.GLS.C3.Layer3.Basic
public import CFSG.GH74.GLS.C3.Prop121.G5Norm
public import CFSG.GH74.GLS.C3.Layer2.L4Setup
public import CFSG.GH74.GLS.C3.Layer2.L5Fin

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Layer3

theorem pattern_map_fusion {G : Type} [Group G] [Finite G]
    (hP : SameInvolutionFusionPattern G (alternatingGroup (Fin 9)))
    {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) :
    ∃ φ : ↥S →* alternatingGroup (Fin 9), Function.Injective φ ∧ IsSylowOf 2 φ.range ⊤ ∧
      (∀ u v : ↥S, orderOf u = 2 → orderOf v = 2 →
        (IsConj (u : G) (v : G) ↔ IsConj (φ u) (φ v))) := by
  obtain ⟨S₁, S', φ₁, hcls⟩ := hP
  have hFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSylow : ∀ {X : Type} [Group X] [Finite X] (T : Sylow 2 X),
      IsSylowOf 2 (T : Subgroup X) ⊤ := by
    intro X _ _ T
    rw [isSylowOf_iff]
    refine ⟨le_top, T.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact T.not_dvd_index
  obtain ⟨k, -, hk⟩ := IsSylowOf.exists_mem_conj (hSylow S₁) hS
  let c : ↥S →* ↥(S₁ : Subgroup G) :=
    { toFun := fun s => ⟨k⁻¹ * s * k, (hk s).1 s.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp only [Subgroup.coe_mul]; group }
  have hcinj : Function.Injective c := by
    intro a b h
    apply Subtype.ext
    have h2 : k⁻¹ * (a : G) * k = k⁻¹ * (b : G) * k :=
      congrArg (fun z : ↥(S₁ : Subgroup G) => (z : G)) h
    simpa using h2
  let φ : ↥S →* alternatingGroup (Fin 9) :=
    ((S' : Subgroup (alternatingGroup (Fin 9))).subtype).comp
      ((φ₁ : ↥(S₁ : Subgroup G) →* ↥(S' : Subgroup (alternatingGroup (Fin 9)))).comp c)
  have hφinj : Function.Injective φ :=
    Subtype.val_injective.comp (φ₁.injective.comp hcinj)
  have hrange : φ.range = (S' : Subgroup (alternatingGroup (Fin 9))) := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact SetLike.coe_mem _
    · intro hy
      obtain ⟨z, hz⟩ := φ₁.surjective ⟨y, hy⟩
      have hzS : k * (z : G) * k⁻¹ ∈ S := by
        rw [hk]
        have : k⁻¹ * (k * (z : G) * k⁻¹) * k = z := by group
        rw [this]
        exact z.2
      refine ⟨⟨k * z * k⁻¹, hzS⟩, ?_⟩
      have hcz : c ⟨k * z * k⁻¹, hzS⟩ = z := by
        apply Subtype.ext
        show k⁻¹ * (k * (z : G) * k⁻¹) * k = z
        group
      show ((φ₁ (c ⟨k * z * k⁻¹, hzS⟩) : ↥(S' : Subgroup (alternatingGroup (Fin 9)))) :
        alternatingGroup (Fin 9)) = y
      rw [hcz, hz]
  have hconj : ∀ a b : G, IsConj a b → IsConj (k⁻¹ * a * k) (k⁻¹ * b * k) := by
    intro a b h
    have := (isConj_map_iff (MulAut.conj k⁻¹) (a := a) (b := b)).2 h
    simpa [MulAut.conj_apply] using this
  have hconj' : ∀ a b : G, IsConj (k⁻¹ * a * k) (k⁻¹ * b * k) → IsConj a b := by
    intro a b h
    have := (isConj_map_iff (MulAut.conj k⁻¹) (a := a) (b := b)).1
    apply this
    simpa [MulAut.conj_apply] using h
  refine ⟨φ, hφinj, ?_, ?_⟩
  · rw [hrange]
    exact hSylow S'
  · intro u v hu hv
    have hu' : orderOf (c u) = 2 := by rw [orderOf_injective c hcinj u]; exact hu
    have hv' : orderOf (c v) = 2 := by rw [orderOf_injective c hcinj v]; exact hv
    have h1 := hcls (c u) (c v) hu' hv'
    constructor
    · intro h
      exact h1.1 (hconj _ _ h)
    · intro h
      exact hconj' _ _ (h1.2 h)

theorem central_nm8
    {S : Type*} [Group S] (φ : S →* alternatingGroup (Fin 9))
    (hsyl : IsSylowOf 2 φ.range ⊤) (hinj : Function.Injective φ) (v : S)
    (hvc : ∀ s : S, s * v = v * s) (hv1 : v ≠ 1) :
    numMoved ((φ v : alternatingGroup (Fin 9)) : Perm (Fin 9)) = 8 := by
  obtain ⟨k, -, hk⟩ := hsyl.exists_mem_conj isSylowOf_S0A
  have hzS0A : (k * φ v * k⁻¹ : alternatingGroup (Fin 9)) ∈ S0A := by
    rw [hk]
    have e : k⁻¹ * (k * φ v * k⁻¹) * k = φ v := by group
    rw [e]
    exact ⟨v, rfl⟩
  have hzS0 : ((k * φ v * k⁻¹ : alternatingGroup (Fin 9)) : Perm (Fin 9)) ∈ S0 := hzS0A
  have hzc : ∀ t ∈ S0, ((k * φ v * k⁻¹ : alternatingGroup (Fin 9)) : Perm (Fin 9)) * t =
      t * ((k * φ v * k⁻¹ : alternatingGroup (Fin 9)) : Perm (Fin 9)) := by
    intro t ht
    have ht' : (⟨t, S0_le_alt ht⟩ : alternatingGroup (Fin 9)) ∈ S0A := mem_S0A.2 ht
    rw [hk] at ht'
    obtain ⟨s, hs⟩ := ht'
    have h1 : φ s * φ v = φ v * φ s := by rw [← map_mul, ← map_mul, hvc s]
    have h2 : (⟨t, S0_le_alt ht⟩ : alternatingGroup (Fin 9)) = k * φ s * k⁻¹ := by
      rw [hs]
      group
    have h3 : (k * φ v * k⁻¹ : alternatingGroup (Fin 9)) *
        (⟨t, S0_le_alt ht⟩ : alternatingGroup (Fin 9)) =
        (⟨t, S0_le_alt ht⟩ : alternatingGroup (Fin 9)) * (k * φ v * k⁻¹) := by
      rw [h2]
      calc k * φ v * k⁻¹ * (k * φ s * k⁻¹) = k * (φ v * φ s) * k⁻¹ := by group
        _ = k * (φ s * φ v) * k⁻¹ := by rw [h1]
        _ = k * φ s * k⁻¹ * (k * φ v * k⁻¹) := by group
    exact congrArg Subtype.val h3
  rcases Z_S0 hzS0 hzc with h1 | h1
  · exfalso
    have h2 : k * φ v * k⁻¹ = 1 := Subtype.ext h1
    have h3 : φ v = 1 := by
      calc φ v = k⁻¹ * (k * φ v * k⁻¹) * k := by group
        _ = 1 := by rw [h2]; group
    exact hv1 (hinj (h3.trans (map_one φ).symm))
  · have h2 := numMoved_conj ((φ v : alternatingGroup (Fin 9)) : Perm (Fin 9))
      (k : Perm (Fin 9))
    have h3 : ((k * φ v * k⁻¹ : alternatingGroup (Fin 9)) : Perm (Fin 9)) =
        (k : Perm (Fin 9)) * (φ v : Perm (Fin 9)) * (k : Perm (Fin 9))⁻¹ := rfl
    rw [← h2, ← h3, h1]
    exact numMoved_yS

section Config

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

theorem not_isConj_x_v5 (h : IsAConfig 5 x K T Q S a) (hT : Nat.card T = 32) :
    ¬ IsConj x (x * (a * x * a⁻¹)) := by
  intro hc
  obtain ⟨e⟩ := nonempty_centralizer_equiv_of_isConj hc
  have hcard := Nat.card_congr e.toEquiv
  have hSle : T ⊔ zpowers a ≤ S := sup_le h.T_lt_S.le (zpowers_le.2 h.a_mem.1)
  have hp : IsPGroup 2 ↥(T ⊔ zpowers a) := IsPGroup.to_le h.sylowS.isPGroup hSle
  have haS1 : a ∈ T ⊔ zpowers a := (le_sup_right : zpowers a ≤ T ⊔ zpowers a) (mem_zpowers a)
  have hlt : T < T ⊔ zpowers a := lt_of_le_of_ne le_sup_left (fun heq => by
    rw [← heq] at haS1
    exact h.a_mem.2.2.1 haS1)
  have hcard' := Subgroup.card_lt_of_lt hlt
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  rw [hk, hT] at hcard'
  have hk6 : 6 ≤ k := by
    by_contra hk6
    have : 2 ^ k ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h7 : 2 ^ 6 ∣ Nat.card ↥(centralizer ({x * (a * x * a⁻¹)} : Set G)) :=
    (pow_dvd_pow 2 hk6).trans (hk ▸ Subgroup.card_dvd_of_le h.sup_le_centralizer_v)
  rw [← hcard] at h7
  have hne : Nat.card ↥(centralizer ({x} : Set G)) ≠ 0 := Nat.card_pos.ne'
  have h8 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).1 h7
  have h9 := h.sylowT.card_eq
  rw [hT, show (32 : ℕ) = 2 ^ 5 by norm_num] at h9
  have h10 : (Nat.card ↥(centralizer ({x} : Set G))).factorization 2 = 5 :=
    (Nat.pow_right_injective (le_refl 2) h9).symm
  omega

structure Psi5 (x a : G) (S : Subgroup G) (hxS : x ∈ S) (hvS : x * (a * x * a⁻¹) ∈ S)
    (ψ : ↥S →* Perm (Fin 9)) : Prop where
  inj : Function.Injective ψ
  mem : ∀ s, ψ s ∈ S0
  surj : ∀ p ∈ S0, ∃ s, ψ s = p
  x_eq : ψ ⟨x, hxS⟩ = emb 5 f1
  v_eq : ψ ⟨x * (a * x * a⁻¹), hvS⟩ = yS
  v_cent : ∀ s : ↥S, s * ⟨x * (a * x * a⁻¹), hvS⟩ = ⟨x * (a * x * a⁻¹), hvS⟩ * s
  conj : ∀ u v : ↥S, orderOf u = 2 → orderOf v = 2 →
    (IsConj (u : G) (v : G) ↔ numMoved (ψ u) = numMoved (ψ v))

theorem exists_psi5
    (h : IsAConfig 5 x K T Q S a) (hT32 : Nat.card T = 32)
    (hfus : SameInvolutionFusionPattern G (alternatingGroup (Fin 9))) :
    ∃ ψ : ↥S →* Perm (Fin 9), Psi5 x a S (h.T_lt_S.le h.x_mem_T)
      (mul_mem (h.T_lt_S.le h.x_mem_T) (mul_mem (mul_mem h.a_mem.1 (h.T_lt_S.le h.x_mem_T))
        (inv_mem h.a_mem.1))) ψ := by
  have hTS : T ≤ S := h.T_lt_S.le
  have hxS : x ∈ S := hTS h.x_mem_T
  obtain ⟨φ, hφinj, hφsyl, hφconj⟩ := pattern_map_fusion hfus h.sylowS
  have hS64 : Nat.card S = 64 := by
    have h1 : Nat.card S = Nat.card φ.range :=
      Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv
    have h2 := hφsyl.card_eq
    rw [Subgroup.card_top, card_A9, Nat.factorization_def _ Nat.prime_two] at h2
    rw [h1, h2]
    decide +kernel
  have hidx : (T.subgroupOf S).index = 2 := by
    have h1 : T.relIndex S * Nat.card (T ⊓ S : Subgroup G) = Nat.card S :=
      Subgroup.relIndex_mul_card T S
    rw [inf_eq_left.2 hTS, hT32, hS64] at h1
    exact (by omega : T.relIndex S = 2)
  set xS : ↥S := ⟨x, hxS⟩ with hxSdef
  have haS : a ∈ S := h.a_mem.1
  set aS : ↥S := ⟨a, haS⟩ with haSdef
  set x'S : ↥S := ⟨a * x * a⁻¹, mul_mem (mul_mem haS hxS) (inv_mem haS)⟩ with hx'Sdef
  have hx'eq : x'S = aS * xS * aS⁻¹ := rfl
  have hne : xS ≠ x'S := fun hc => h.a_conj_x_ne (congrArg Subtype.val hc).symm
  have hsq : xS * xS = 1 := Subtype.ext (by
    show x * x = 1
    rw [← sq]
    exact h.x_sq)
  have hkey : ∀ s : ↥S, s * xS * s⁻¹ = xS ∨ s * xS * s⁻¹ = x'S := by
    intro s
    by_cases hs : (s : G) ∈ T
    · left
      have hc : (s : G) * x = x * (s : G) := mem_centralizer_singleton_iff.1 (h.T_le_C hs)
      have : s * xS = xS * s := Subtype.ext hc
      rw [this]
      group
    · right
      have haT : (a : G) ∉ T := h.a_mem.2.2.1
      have h1 : aS⁻¹ * s ∈ T.subgroupOf S := by
        rw [mul_mem_iff_of_index_two hidx]
        constructor
        · intro hh
          have h2 : (a : G)⁻¹ ∈ T := hh
          exact absurd (inv_mem_iff.1 h2) haT
        · intro hh
          exact absurd hh hs
      have hcT : ((aS⁻¹ * s : ↥S) : G) ∈ T := h1
      have hc : ((aS⁻¹ * s : ↥S) : G) * x = x * ((aS⁻¹ * s : ↥S) : G) :=
        mem_centralizer_singleton_iff.1 (h.T_le_C hcT)
      have hc' : (aS⁻¹ * s) * xS = xS * (aS⁻¹ * s) := Subtype.ext hc
      have hs' : s = aS * (aS⁻¹ * s) := by group
      rw [hx'eq]
      calc s * xS * s⁻¹ = aS * ((aS⁻¹ * s) * xS * (aS⁻¹ * s)⁻¹) * aS⁻¹ := by group
        _ = aS * xS * aS⁻¹ := by rw [hc']; group
  have hcl : ∀ s : ↥S, (s * xS * s⁻¹ = xS ∨ s * xS * s⁻¹ = x'S) ∧
      (s * x'S * s⁻¹ = xS ∨ s * x'S * s⁻¹ = x'S) := by
    intro s
    refine ⟨hkey s, ?_⟩
    have e : s * x'S * s⁻¹ = (s * aS) * xS * (s * aS)⁻¹ := by rw [hx'eq]; group
    rw [e]
    exact hkey (s * aS)
  have hxx' : xS * x'S = x'S * xS := by
    apply Subtype.ext
    exact h.conj_x_comm h.x_mem_T
  obtain ⟨vS, hvS⟩ : ∃ vS : ↥S, vS = xS * x'S := ⟨_, rfl⟩
  have hvc' : ∀ s : ↥S, s * vS * s⁻¹ = vS := by
    intro s
    obtain ⟨h1, h2⟩ := hcl s
    have hconj : s * vS * s⁻¹ = (s * xS * s⁻¹) * (s * x'S * s⁻¹) := by rw [hvS]; group
    rw [hconj]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exfalso
      apply hne
      have : s * xS * s⁻¹ = s * x'S * s⁻¹ := h1.trans h2.symm
      calc xS = s⁻¹ * (s * xS * s⁻¹) * s := by group
        _ = s⁻¹ * (s * x'S * s⁻¹) * s := by rw [this]
        _ = x'S := by group
    · rw [h1, h2, hvS]
    · rw [h1, h2, hvS, hxx']
    · exfalso
      apply hne
      have : s * xS * s⁻¹ = s * x'S * s⁻¹ := h1.trans h2.symm
      calc xS = s⁻¹ * (s * xS * s⁻¹) * s := by group
        _ = s⁻¹ * (s * x'S * s⁻¹) * s := by rw [this]
        _ = x'S := by group
  have hvc : ∀ s : ↥S, s * vS = vS * s := by
    intro s
    calc s * vS = (s * vS * s⁻¹) * s := by group
      _ = vS * s := by rw [hvc' s]
  have hx'sq : x'S * x'S = 1 := by
    apply Subtype.ext
    show (a * x * a⁻¹) * (a * x * a⁻¹) = 1
    calc a * x * a⁻¹ * (a * x * a⁻¹) = a * (x * x) * a⁻¹ := by group
      _ = 1 := by rw [L4.x_mul_self h]; group
  have hvsq : vS * vS = 1 := by
    rw [hvS]
    calc xS * x'S * (xS * x'S) = xS * (x'S * xS) * x'S := by group
      _ = xS * (xS * x'S) * x'S := by rw [hxx']
      _ = (xS * xS) * (x'S * x'S) := by group
      _ = 1 := by rw [hsq, hx'sq, one_mul]
  have hvG : (vS : G) = x * (a * x * a⁻¹) := by rw [hvS]; rfl
  have hv1 : vS ≠ 1 := by
    intro h1
    exact L4.v_ne_one h (hvG.symm.trans (congrArg Subtype.val h1))
  have hvord : orderOf vS = 2 := orderOf_eq_prime (by rw [sq]; exact hvsq) hv1
  have hxord : orderOf xS = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hsq) (fun hc => h.x_ne_one (congrArg Subtype.val hc))
  have hφxord : orderOf (φ xS) = 2 := by rw [orderOf_injective φ hφinj]; exact hxord
  have hφvord : orderOf (φ vS) = 2 := by rw [orderOf_injective φ hφinj]; exact hvord
  have hnm8 : numMoved ((φ vS : alternatingGroup (Fin 9)) : Perm (Fin 9)) = 8 :=
    central_nm8 φ hφsyl hφinj vS hvc hv1
  have hnm : numMoved ((φ xS : alternatingGroup (Fin 9)) : Perm (Fin 9)) = 4 := by
    rcases numMoved_eq_of_involution_alternating 9 (by norm_num) (φ xS) hφxord with h4 | h8
    · exact h4
    · exfalso
      have hc : IsConj (φ xS) (φ vS) :=
        isConj_alternating_of_numMoved_eq 9 _ _ hφxord hφvord (by rw [h8, hnm8])
      have hc' := (hφconj xS vS hxord hvord).2 hc
      exact not_isConj_x_v5 h hT32 (by rw [← hvG]; exact hc')
  obtain ⟨ψ, hψinj, hψnm, hψS0, hψsurj, hψx⟩ :=
    normalize φ hφinj hφsyl xS x'S hne hsq hnm hcl
  have hψv : ψ vS = yS := by
    have hc : ∀ t ∈ S0, ψ vS * t = t * ψ vS := by
      intro t ht
      obtain ⟨s, rfl⟩ := hψsurj t ht
      rw [← map_mul, ← map_mul, hvc s]
    rcases Z_S0 (hψS0 vS) hc with h1 | h1
    · exfalso
      exact hv1 (hψinj (h1.trans (map_one ψ).symm))
    · exact h1
  have hvS_eq : (⟨x * (a * x * a⁻¹), mul_mem hxS (mul_mem (mul_mem haS hxS) (inv_mem haS))⟩ :
      ↥S) = vS := Subtype.ext hvG.symm
  refine ⟨ψ, hψinj, hψS0, hψsurj, hψx, ?_, ?_, ?_⟩
  · exact (congrArg ψ hvS_eq).trans hψv
  · intro s
    rw [hvS_eq]
    exact hvc s
  intro u w hu hw
  have hφu : orderOf (φ u) = 2 := by rw [orderOf_injective φ hφinj]; exact hu
  have hφw : orderOf (φ w) = 2 := by rw [orderOf_injective φ hφinj]; exact hw
  rw [hψnm, hψnm]
  constructor
  · intro huw
    exact numMoved_eq_of_isConj_alternating 9 ((hφconj u w hu hw).1 huw)
  · intro hnm'
    exact (hφconj u w hu hw).2 (isConj_alternating_of_numMoved_eq 9 _ _ hφu hφw hnm')

end Config

end CFSG.GH74.GLS.C3.Layer2.L5
