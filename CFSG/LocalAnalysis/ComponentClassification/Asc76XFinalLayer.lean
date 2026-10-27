module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma315
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.Goldschmidt.Steps.GoldType

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.LocalCores

variable {E : Type} [Group E] [Finite E]

theorem center_eq_bot_of (hO : ∀ N : Subgroup E, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hO2 : ∀ N : Subgroup E, N.Normal → IsPGroup 2 N → N = ⊥) : center E = ⊥ := by
  have hnormal : ∀ y ∈ center E, (zpowers y).Normal := fun y hy =>
    ⟨fun n hn g => by
      have hnc : n ∈ center E := (zpowers_le.mpr hy) hn
      have h1 := mem_center_iff.mp hnc g
      rw [h1, mul_inv_cancel_right]
      exact hn⟩
  rw [eq_bot_iff]
  intro x hx
  rw [mem_bot]
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hy1 : (x ^ 2 ^ a) ^ m = 1 := by
    rw [← pow_mul, ← hn, pow_orderOf_eq_one]
  have hyodd : Odd (Nat.card (zpowers (x ^ 2 ^ a))) := by
    rw [Nat.card_zpowers]
    exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hy1)
  have hy : x ^ 2 ^ a = 1 := by
    have h1 := hO _ (hnormal _ (pow_mem hx _)) hyodd
    have h2 : x ^ 2 ^ a ∈ zpowers (x ^ 2 ^ a) := mem_zpowers _
    rwa [h1, mem_bot] at h2
  have h1 := hO2 _ (hnormal x hx) (isPGroup_zpowers_of_two_element hy)
  have h2 : x ∈ zpowers x := mem_zpowers x
  rwa [h1, mem_bot] at h2

theorem goldschmidtSimpleType_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : goldschmidtSimpleType B) : goldschmidtSimpleType A := by
  rcases h with ⟨f, hf, ⟨φ⟩⟩ | ⟨n, hn, ⟨φ⟩⟩ | ⟨f, hf, ⟨φ⟩⟩ | ⟨p, f, hp, hp2, hf, h5, h8, ⟨φ⟩⟩ |
    ⟨m, hm, hcard⟩ | ⟨⟨φ⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.trans φ⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.trans φ⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hf, ⟨e.trans φ⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, h5, h8, ⟨e.trans φ⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm, (Nat.card_congr e.toEquiv).trans hcard⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans φ⟩))))

omit [Finite E] in
theorem sq_eq_one_of_mem_omega1 {P : Subgroup E} (hab : IsMulCommutative (omega1 P)) {x : E}
    (hx : x ∈ omega1 P) : x ^ 2 = 1 := by
  refine (isElemAbelian_closure (s := {x | x ∈ P ∧ x ^ 2 = 1}) (fun y hy => hy.2)
    (fun a ha b hb => ?_)).2 x hx
  have h1 : (⟨a, subset_closure ha⟩ : ↥(omega1 P)) * ⟨b, subset_closure hb⟩ =
      ⟨b, subset_closure hb⟩ * ⟨a, subset_closure ha⟩ := hab.is_comm.comm _ _
  simpa using congrArg Subtype.val h1

omit [Finite E] in
theorem omega1_inf_eq {P L : Subgroup E} (hab : IsMulCommutative (omega1 P)) :
    omega1 (P ⊓ L) = omega1 P ⊓ L := by
  apply le_antisymm
  · refine (closure_le _).mpr fun x hx => ?_
    exact mem_inf.mpr ⟨mem_omega1_of_sq (mem_inf.mp hx.1).1 hx.2, (mem_inf.mp hx.1).2⟩
  · intro x hx
    obtain ⟨hxP, hxL⟩ := mem_inf.mp hx
    exact mem_omega1_of_sq (mem_inf.mpr ⟨omega1_le P hxP, hxL⟩) (sq_eq_one_of_mem_omega1 hab hxP)

section Layer

variable (hL : layer E = ⊤) (hZE : center E = ⊥)
include hL hZE

theorem center_component_eq_bot {K : Subgroup E} (hK : IsComponent K) : center K = ⊥ := by
  have h := center_component_le_centralizer_layer hK
  rw [hL, coe_top, centralizer_univ, hZE, le_bot_iff,
    map_eq_bot_iff_of_injective _ K.subtype_injective] at h
  exact h

theorem isSimpleGroup_component {K : Subgroup E} (hK : IsComponent K) : IsSimpleGroup K := by
  have e : ↥K ⧸ center ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq (center_component_eq_bot hL hZE hK)).trans
      QuotientGroup.quotientBot
  exact (MulEquiv.isSimpleGroup_congr e).mp hK.1.2.1

theorem layerMul_bijective : Function.Bijective (layerMul E) := by
  refine ⟨(injective_iff_map_eq_one _).mpr fun x hx => ?_, fun g => ?_⟩
  · funext K
    have h : x K ∈ center K.1 := layerMul_ker_le (G := E) hx K (Set.mem_univ K)
    rw [center_component_eq_bot hL hZE K.2, mem_bot] at h
    exact h
  · exact exists_layerMul_eq (by rw [hL]; exact mem_top g)

noncomputable def layerEquiv : (∀ K : ComponentIndex E, K.1) ≃* E :=
  MulEquiv.ofBijective (layerMul E) (layerMul_bijective hL hZE)

noncomputable def layerProj (K : ComponentIndex E) : E →* K.1 :=
  (Pi.evalMonoidHom (fun L : ComponentIndex E => ↥L.1) K).comp
    (layerEquiv hL hZE).symm.toMonoidHom

theorem layerProj_of_mem (K : ComponentIndex E) {k : E} (hk : k ∈ K.1) :
    (layerProj hL hZE K k : E) = k := by
  have h : (layerEquiv hL hZE).symm k = Pi.mulSingle K ⟨k, hk⟩ := by
    apply (layerEquiv hL hZE).injective
    rw [MulEquiv.apply_symm_apply]
    change k = layerMul E (Pi.mulSingle K ⟨k, hk⟩)
    rw [layerMul_mulSingle]
  change ((layerEquiv hL hZE).symm k K : E) = k
  rw [h, Pi.mulSingle_eq_same]

theorem exists_eq_layerProj_mul (x : E) (K : ComponentIndex E) :
    ∃ u : E, x = (layerProj hL hZE K x : E) * u ∧ ∀ k ∈ K.1, k * u = u * k := by
  set c := (layerEquiv hL hZE).symm x with hc
  have hx : x = layerMul E c := by
    change x = layerEquiv hL hZE c
    rw [hc, MulEquiv.apply_symm_apply]
  refine ⟨layerMul E (Function.update c K 1), ?_, fun k hk => (commute_layerMul_update c K hk).eq⟩
  conv_lhs => rw [hx, layerMul_eq_mul_update c K]
  rfl

theorem exists_layerProj_ne_one {x : E} (hx : x ≠ 1) :
    ∃ K : ComponentIndex E, layerProj hL hZE K x ≠ 1 := by
  by_contra h
  push Not at h
  apply hx
  have hc : (layerEquiv hL hZE).symm x = 1 := funext fun K => h K
  have := congrArg (layerEquiv hL hZE) hc
  rwa [MulEquiv.apply_symm_apply, map_one] at this

theorem layerProj_mem_of_mem {P : Subgroup E} (hP : IsSylowOf 2 P ⊤) (K : ComponentIndex E)
    {x : E} (hx : x ∈ P) : (layerProj hL hZE K x : E) ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKn : K.1.Normal := component_normal_of_layer_eq_top hL K.2
  have hPK : IsSylowOf 2 (P ⊓ K.1) K.1 :=
    isSylowOf_inf le_top (by rw [normalizer_eq_top_iff.mpr hKn]) hP
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (isSylowOf_iff_card.mp hP).2
  set Q := (P.map (layerProj hL hZE K)).map K.1.subtype with hQ
  have hQ2 : IsPGroup 2 Q := (hP2.map _).map _
  have hQK : Q ≤ K.1 := map_subtype_le _
  have hPQ : P ⊓ K.1 ≤ Q := fun k hk => ⟨layerProj hL hZE K k, ⟨k, (mem_inf.mp hk).1, rfl⟩,
    layerProj_of_mem hL hZE K (mem_inf.mp hk).2⟩
  have heq := eq_of_isSylowOf_le hPK hQ2 hQK hPQ
  have hmem : (layerProj hL hZE K x : E) ∈ Q := ⟨layerProj hL hZE K x, ⟨x, hx, rfl⟩, rfl⟩
  rw [heq] at hmem
  exact (mem_inf.mp hmem).1

theorem card_inf_ge_and_exists_conj
    (hC : ∀ K : Subgroup E, IsComponent K → goldschmidtSimpleType (↥K ⧸ center ↥K))
    {P : Subgroup E} (hP : IsSylowOf 2 P ⊤) (hab : IsMulCommutative (omega1 P)) {K : Subgroup E}
    (hK : IsComponent K) :
    4 ≤ Nat.card ↥(omega1 P ⊓ K) ∧ ∀ x ∈ omega1 P ⊓ K, ∀ y ∈ omega1 P ⊓ K, x ≠ 1 → y ≠ 1 →
      ∃ n ∈ K, n⁻¹ * x * n = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKn : K.Normal := component_normal_of_layer_eq_top hL hK
  have hPK : IsSylowOf 2 (P ⊓ K) K :=
    isSylowOf_inf le_top (by rw [normalizer_eq_top_iff.mpr hKn]) hP
  obtain ⟨Q, hQ⟩ := hPK
  have := isSimpleGroup_component hL hZE hK
  have e : ↥K ⧸ center ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq (center_component_eq_bot hL hZE hK)).trans
      QuotientGroup.quotientBot
  have hgold : goldschmidtSimpleType ↥K := goldschmidtSimpleType_of_mulEquiv e.symm (hC K hK)
  have hmap : (CFSG.Goldschmidt.Omega1 (Q : Subgroup ↥K)).map K.subtype = omega1 P ⊓ K := by
    rw [← omega1_inf_eq hab, ← hQ]
    change (Subgroup.closure _).map K.subtype = Subgroup.closure _
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨t, ⟨htQ, ht2⟩, rfl⟩
      exact ⟨⟨t, htQ, rfl⟩, by simpa using congrArg Subtype.val ht2⟩
    · rintro ⟨⟨t, htQ, rfl⟩, hx2⟩
      exact ⟨t, ⟨htQ, Subtype.ext (by simpa using hx2)⟩, rfl⟩
  have hcomm : IsMulCommutative (CFSG.Goldschmidt.Omega1 (Q : Subgroup ↥K)) := by
    refine ⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩
    have ha : ((a : ↥K) : E) ∈ omega1 P := by
      have h : ((a : ↥K) : E) ∈ omega1 P ⊓ K := by rw [← hmap]; exact ⟨a, a.2, rfl⟩
      exact (mem_inf.mp h).1
    have hb : ((b : ↥K) : E) ∈ omega1 P := by
      have h : ((b : ↥K) : E) ∈ omega1 P ⊓ K := by rw [← hmap]; exact ⟨b, b.2, rfl⟩
      exact (mem_inf.mp h).1
    have h1 : (⟨_, ha⟩ : ↥(omega1 P)) * ⟨_, hb⟩ = ⟨_, hb⟩ * ⟨_, ha⟩ := hab.is_comm.comm _ _
    simpa using congrArg Subtype.val h1
  obtain ⟨h4, htrans⟩ := CFSG.Goldschmidt.N11b ↥K hgold Q hcomm
  refine ⟨?_, fun x hx y hy hx1 hy1 => ?_⟩
  · rw [← hmap, card_map_of_injective K.subtype_injective]
    exact h4
  · rw [← hmap] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hx1' : x' ≠ 1 := fun h => hx1 (by rw [h]; rfl)
    have hy1' : y' ≠ 1 := fun h => hy1 (by rw [h]; rfl)
    obtain ⟨n, -, hn⟩ := htrans x' hx' y' hy' hx1' hy1'
    exact ⟨n, n.2, by simpa using congrArg Subtype.val hn⟩

theorem exists_pure_component
    (hC : ∀ K : Subgroup E, IsComponent K → goldschmidtSimpleType (↥K ⧸ center ↥K))
    {P : Subgroup E} (hP : IsSylowOf 2 P ⊤) (hab : IsMulCommutative (omega1 P))
    {A₁ B₁ : Subgroup E} (hAB : A₁ ⊔ B₁ = omega1 P) (hA1 : A₁ ≠ ⊥)
    (hpure : ∀ z m : E, (z ∈ A₁ ∨ z ∈ B₁) → m⁻¹ * z * m ∈ omega1 P →
      m⁻¹ * z * m ∈ A₁ ∨ m⁻¹ * z * m ∈ B₁) :
    ∃ K : Subgroup E, IsComponent K ∧ omega1 P ⊓ K ≠ ⊥ ∧
      (omega1 P ⊓ K ≤ A₁ ∨ omega1 P ⊓ K ≤ B₁) := by
  have hcomm : ∀ a ∈ omega1 P, ∀ b ∈ omega1 P, a * b = b * a := fun a ha b hb => by
    have h1 : (⟨a, ha⟩ : ↥(omega1 P)) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := hab.is_comm.comm _ _
    simpa using congrArg Subtype.val h1
  have hAZ : A₁ ≤ omega1 P := hAB ▸ le_sup_left
  have hBZ : B₁ ≤ omega1 P := hAB ▸ le_sup_right
  obtain ⟨⟨r, hr⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hrZ : r ∈ omega1 P := hAZ hr
  obtain ⟨K, hK⟩ := exists_layerProj_ne_one hL hZE hr1'
  obtain ⟨u, hru, hu⟩ := exists_eq_layerProj_mul hL hZE r K
  set x : E := (layerProj hL hZE K r : E) with hxdef
  have hx1 : x ≠ 1 := fun h => hK (Subtype.ext h)
  have hxK : x ∈ K.1 := (layerProj hL hZE K r).2
  have hxP : x ∈ P := layerProj_mem_of_mem hL hZE hP K (omega1_le P hrZ)
  have hx2 : x ^ 2 = 1 := by
    have h1 : layerProj hL hZE K (r ^ 2) = 1 := by rw [sq_eq_one_of_mem_omega1 hab hrZ, map_one]
    rw [map_pow] at h1
    simpa [hxdef] using congrArg Subtype.val h1
  have hxZ : x ∈ omega1 P := mem_omega1_of_sq hxP hx2
  have hxW : x ∈ omega1 P ⊓ K.1 := mem_inf.mpr ⟨hxZ, hxK⟩
  obtain ⟨h4, htrans⟩ := card_inf_ge_and_exists_conj hL hZE hC hP hab K.2
  have hconj : ∀ y ∈ omega1 P ⊓ K.1, y ≠ 1 → y * x⁻¹ * r ∈ A₁ ∨ y * x⁻¹ * r ∈ B₁ := by
    intro y hy hy1
    obtain ⟨n, hnK, hn⟩ := htrans x hxW y hy hx1 hy1
    have hun : n⁻¹ * u * n = u := by rw [mul_assoc, ← hu n hnK, inv_mul_cancel_left]
    have e : n⁻¹ * r * n = y * x⁻¹ * r := by
      calc n⁻¹ * r * n = (n⁻¹ * x * n) * (n⁻¹ * u * n) := by
            conv_lhs => rw [hru]
            group
        _ = y * u := by rw [hn, hun]
        _ = y * x⁻¹ * r := by
            conv_rhs => rw [hru]
            group
    have hmem : n⁻¹ * r * n ∈ omega1 P := by
      rw [e]
      exact mul_mem (mul_mem (mem_inf.mp hy).1 (inv_mem hxZ)) hrZ
    have := hpure r n (Or.inl hr) hmem
    rwa [e] at this
  have hs : 1 < (((omega1 P ⊓ K.1 : Subgroup E) : Set E) \ {1, x}).ncard := by
    have h1 := Set.le_ncard_sdiff ({1, x} : Set E) ((omega1 P ⊓ K.1 : Subgroup E) : Set E)
    have h2 : ({1, x} : Set E).ncard ≤ 2 := by
      calc ({1, x} : Set E).ncard ≤ ({x} : Set E).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    have hW : Nat.card ↥(omega1 P ⊓ K.1) = ((omega1 P ⊓ K.1 : Subgroup E) : Set E).ncard := rfl
    omega
  obtain ⟨y₁, y₂, hy₁, hy₂, hne⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp hs
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
    SetLike.mem_coe] at hy₁ hy₂
  obtain ⟨hy₁W, hy₁1, hy₁x⟩ := hy₁
  obtain ⟨hy₂W, hy₂1, hy₂x⟩ := hy₂
  have hpw : ∃ w ∈ omega1 P ⊓ K.1, w ≠ 1 ∧ (w ∈ A₁ ∨ w ∈ B₁) := by
    have hyA : ∀ y ∈ omega1 P ⊓ K.1, y ≠ x → y * x⁻¹ * r ∈ A₁ →
        ∃ w ∈ omega1 P ⊓ K.1, w ≠ 1 ∧ (w ∈ A₁ ∨ w ∈ B₁) := by
      intro y hy hyx h
      refine ⟨y * x⁻¹, mul_mem hy (inv_mem hxW), fun h' => hyx (mul_inv_eq_one.mp h'), Or.inl ?_⟩
      have := mul_mem h (inv_mem hr)
      simpa [mul_assoc] using this
    rcases hconj y₁ hy₁W hy₁1 with h1 | h1
    · exact hyA y₁ hy₁W hy₁x h1
    rcases hconj y₂ hy₂W hy₂1 with h2 | h2
    · exact hyA y₂ hy₂W hy₂x h2
    refine ⟨y₁⁻¹ * y₂, mul_mem (inv_mem hy₁W) hy₂W, fun h' => hne (inv_mul_eq_one.mp h'),
      Or.inr ?_⟩
    have h3 := mul_mem (inv_mem h1) h2
    have hy₁Z := (mem_inf.mp hy₁W).1
    have hy₂Z := (mem_inf.mp hy₂W).1
    have e : (y₁ * x⁻¹ * r)⁻¹ * (y₂ * x⁻¹ * r) = y₁⁻¹ * y₂ := by
      have hw : y₁⁻¹ * y₂ ∈ omega1 P := mul_mem (inv_mem hy₁Z) hy₂Z
      set w := y₁⁻¹ * y₂ with hwdef
      have hxw : x * w = w * x := hcomm _ hxZ _ hw
      have hrw : w * r = r * w := (hcomm _ hrZ _ hw).symm
      calc (y₁ * x⁻¹ * r)⁻¹ * (y₂ * x⁻¹ * r) = r⁻¹ * ((x * w) * x⁻¹) * r := by
            rw [hwdef]; group
        _ = r⁻¹ * ((w * x) * x⁻¹) * r := by rw [hxw]
        _ = r⁻¹ * (w * r) := by group
        _ = r⁻¹ * (r * w) := by rw [hrw]
        _ = w := by group
    rwa [e] at h3
  obtain ⟨w, hwW, hw1, hwp⟩ := hpw
  have hall : ∀ v ∈ omega1 P ⊓ K.1, v ∈ A₁ ∨ v ∈ B₁ := by
    intro v hv
    by_cases hv1 : v = 1
    · rw [hv1]
      exact Or.inl (one_mem _)
    obtain ⟨n, -, hn⟩ := htrans w hwW v hv hw1 hv1
    have := hpure w n hwp (by rw [hn]; exact (mem_inf.mp hv).1)
    rwa [hn] at this
  refine ⟨K.1, K.2, fun h => hx1 (by rw [← mem_bot, ← h]; exact hxW), ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hnA, hnB⟩ := hcon
  obtain ⟨a, haW, haA⟩ : ∃ a ∈ omega1 P ⊓ K.1, a ∉ A₁ := by
    by_contra h
    push Not at h
    exact hnA h
  obtain ⟨b, hbW, hbB⟩ : ∃ b ∈ omega1 P ⊓ K.1, b ∉ B₁ := by
    by_contra h
    push Not at h
    exact hnB h
  have haB : a ∈ B₁ := (hall a haW).resolve_left haA
  have hbA : b ∈ A₁ := (hall b hbW).resolve_right hbB
  rcases hall (a * b) (mul_mem haW hbW) with h | h
  · exact haA (by simpa using mul_mem h (inv_mem hbA))
  · exact hbB (by simpa using mul_mem (inv_mem haB) h)

theorem map_eq_of_forall_fix
    (hC : ∀ K : Subgroup E, IsComponent K → goldschmidtSimpleType (↥K ⧸ center ↥K))
    {P : Subgroup E} (hP : IsSylowOf 2 P ⊤) (hab : IsMulCommutative (omega1 P)) (ψ : E ≃* E)
    (hψ : ∀ z ∈ omega1 P, ψ z = z) {K : Subgroup E} (hK : IsComponent K) :
    K.map ψ.toMonoidHom = K := by
  have hK' := isComponent_map_mulEquiv ψ hK
  rcases distinct_components_commute hK' hK with h | h
  · exact h
  · exfalso
    obtain ⟨h4, -⟩ := card_inf_ge_and_exists_conj hL hZE hC hP hab hK
    have hW : omega1 P ⊓ K = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨hwZ, hwK⟩ := mem_inf.mp hw
      have hwK' : w ∈ K.map ψ.toMonoidHom := ⟨w, hwK, hψ w hwZ⟩
      have hcen : (⟨w, hwK⟩ : ↥K) ∈ center ↥K := mem_center_iff.mpr fun k => Subtype.ext (by
        have h1 := commutator_mem_commutator hwK' k.2
        rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        simpa using h1.symm)
      rw [center_component_eq_bot hL hZE hK, mem_bot] at hcen
      rw [mem_bot]
      exact congrArg Subtype.val hcen
    rw [hW, card_bot] at h4
    omega

end Layer

omit [Finite E] in
theorem false_of_pure_component {P A₁ B₁ K : Subgroup E} (hAB : A₁ ⊔ B₁ = omega1 P)
    (hinf : A₁ ⊓ B₁ = ⊥) (hW : omega1 P ⊓ K ≠ ⊥) (hpure : omega1 P ⊓ K ≤ A₁ ∨ omega1 P ⊓ K ≤ B₁)
    (ψ : E ≃* E) (hψK : K.map ψ.toMonoidHom = K) (hψA : A₁.map ψ.toMonoidHom = B₁) : False := by
  have hAZ : A₁ ≤ omega1 P := hAB ▸ le_sup_left
  have hBZ : B₁ ≤ omega1 P := hAB ▸ le_sup_right
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  obtain ⟨hwZ, hwK⟩ := mem_inf.mp hw
  rcases hpure with hA | hB
  ·
    have h1 : ψ w ∈ B₁ := by rw [← hψA]; exact ⟨w, hA hw, rfl⟩
    have h2 : ψ w ∈ K := by rw [← hψK]; exact ⟨w, hwK, rfl⟩
    have h3 : ψ w ∈ A₁ := hA (mem_inf.mpr ⟨hBZ h1, h2⟩)
    have h4 : ψ w ∈ A₁ ⊓ B₁ := mem_inf.mpr ⟨h3, h1⟩
    rw [hinf, mem_bot, map_eq_one_iff ψ ψ.injective] at h4
    exact hw1' h4
  ·
    have h1 : w ∈ A₁.map ψ.toMonoidHom := by rw [hψA]; exact hB hw
    obtain ⟨a, haA, hau⟩ := h1
    have h2 : w ∈ K.map ψ.toMonoidHom := by rw [hψK]; exact hwK
    obtain ⟨k, hkK, hku⟩ := h2
    have hak : a = k := ψ.injective (hau.trans hku.symm)
    have h3 : a ∈ B₁ := hB (mem_inf.mpr ⟨hAZ haA, hak ▸ hkK⟩)
    have h4 : a ∈ A₁ ⊓ B₁ := mem_inf.mpr ⟨haA, h3⟩
    rw [hinf, mem_bot] at h4
    apply hw1'
    rw [← hau, h4]
    exact map_one _


end CFSG.ComponentClassification.Asc76X
