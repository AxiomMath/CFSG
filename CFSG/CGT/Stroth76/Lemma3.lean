module

public import CFSG.CGT.Stroth76.Lemma3Data
public import CFSG.CGT.Stroth76.SylowCw
public import CFSG.CGT.Stroth76.Lemma1Data
public import CFSG.CGT.Stroth76.Lemma7Two
public import CFSG.CGT.Stroth76.NoInv

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77.Arch76

theorem card_F8_subtype : Fintype.card {p : Sc8 // p ∈ F8} = 16 := by decide +kernel

theorem co_four_nsmul_eq_zero : ∀ v : Co, 4 • v = 0 := by decide

theorem smul8_self_fst (p : Sc8) (h0 : p.2 = 0) : (smul8 p p).1 = p.1 + p.1 := by
  obtain ⟨v, d⟩ := p
  simp only at h0
  subst h0
  simp [smul8, dact8, pw8, dinv]

theorem card_snd_zero_or_u : Fintype.card {p : Sc8 // p.2 = 0 ∨ p.2 = (0, 0, 1)} = 256 := by
  decide +kernel

theorem pow_four_of_mem_configA {X : Type*} [Group X] (K : Config X) {c : X} (hc : c ∈ K.A) :
    c ^ 4 = 1 := by
  obtain ⟨v, rfl⟩ := K.exists_ev hc
  rw [← K.ev_nsmul, co_four_nsmul_eq_zero, K.ev_zero]

namespace ShapeII

variable {G : Type*} [Group G] [Finite G] {K : Config G} (P : ShapeII K)

theorem sElt8_comm {p q : Sc8} (h : smul8 p q = smul8 q p) :
    P.sElt8 p * P.sElt8 q = P.sElt8 q * P.sElt8 p := by
  rw [← P.sElt8_mul, ← P.sElt8_mul, h]

theorem sElt8_one8 : P.sElt8 one8 = 1 := P.sElt8_zero

theorem sElt8_z8 : P.sElt8 z8 = (K.x * K.y) ^ 2 := by
  rw [show z8 = ((0, 4, 4), 0) from rfl, P.sElt8_ev, P.x_eq, P.y_eq, ← P.ev8_add, ← P.ev8_nsmul]
  rfl

theorem sElt8_w8 : P.sElt8 w8 = K.w := by
  rw [show w8 = ((1, 0, 0), 0) from rfl, P.sElt8_ev, P.ev8_w]

theorem sElt8_uv8 : P.sElt8 uv8 = K.uv := P.sElt8_gen_uv
theorem sElt8_u8 : P.sElt8 u8 = K.u := P.sElt8_gen_u

theorem sElt8_wu8 : P.sElt8 wu8 = K.w * K.u := by
  rw [show wu8 = smul8 ((1, 0, 0), 0) (0, (0, 0, 1)) by decide, P.sElt8_mul, P.sElt8_ev,
    P.ev8_w, P.sElt8_gen_u]

theorem sElt8_xyuv8 : P.sElt8 xyuv8 = K.x * K.y * K.uv := by
  rw [show xyuv8 = smul8 ((0, 2, 2), 0) (0, (1, 0, 0)) by decide, P.sElt8_mul, P.sElt8_ev,
    P.sElt8_gen_uv, P.x_eq, P.y_eq, ← P.ev8_add]
  rfl

theorem F8_mem_iff_mul {p q : Sc8} (hp : p ∈ F8) (hq : q ∈ F8) : smul8 p q ∈ F8 := by
  have h := List.all_eq_true.1 F8_closed p hp
  have h' := List.all_eq_true.1 h q hq
  simpa using h'

theorem F8_mul_self {p : Sc8} (hp : p ∈ F8) : smul8 p p = one8 := by
  have h := List.all_eq_true.1 F8_inv p hp
  simpa using h

theorem F8_comm' {p q : Sc8} (hp : p ∈ F8) (hq : q ∈ F8) : smul8 p q = smul8 q p := by
  have h := List.all_eq_true.1 F8_comm p hp
  have h' := List.all_eq_true.1 h q hq
  simpa using h'

@[expose] def Fsub : Subgroup G where
  carrier := {g | ∃ p ∈ F8, P.sElt8 p = g}
  mul_mem' := by
    rintro _ _ ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
    exact ⟨smul8 p q, F8_mem_iff_mul hp hq, P.sElt8_mul p q⟩
  one_mem' := ⟨one8, one8_mem_F8, P.sElt8_one8⟩
  inv_mem' := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨p, hp, ?_⟩
    refine (eq_inv_of_mul_eq_one_left ?_)
    rw [← P.sElt8_mul, F8_mul_self hp, P.sElt8_one8]

theorem card_Fsub : Nat.card P.Fsub = 16 := by
  have hbij : Function.Bijective
      (fun p : {p : Sc8 // p ∈ F8} => (⟨P.sElt8 p, ⟨p, p.2, rfl⟩⟩ : P.Fsub)) :=
    ⟨fun p q h => Subtype.ext (P.sElt8_injective (congrArg Subtype.val h)), fun ⟨g, p, hp, hg⟩ =>
      ⟨⟨p, hp⟩, Subtype.ext hg⟩⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, card_F8_subtype]

theorem Fsub_inv {f : G} (hf : f ∈ P.Fsub) : f * f = 1 := by
  obtain ⟨p, hp, rfl⟩ := hf
  rw [← P.sElt8_mul, F8_mul_self hp, P.sElt8_one8]

theorem Fsub_comm {f g : G} (hf : f ∈ P.Fsub) (hg : g ∈ P.Fsub) : f * g = g * f := by
  obtain ⟨p, hp, rfl⟩ := hf
  obtain ⟨q, hq, rfl⟩ := hg
  exact P.sElt8_comm (F8_comm' hp hq)

theorem r0_mem_Fsub : P.sElt8 r0_8 ∈ P.Fsub := ⟨r0_8, r0_mem_F8, rfl⟩

theorem mem_C_iff (p : Sc8) : P.sElt8 p ∈ P.C ↔ p.2 = 0 := by
  constructor
  · intro h
    apply P.eq_zero_of_dElt_mem
    have : dElt K p.2 = (P.ev8 p.1)⁻¹ * P.sElt8 p := by simp [sElt8]
    rw [this]
    exact P.C.mul_mem (P.C.inv_mem (P.ev8_mem _)) h
  · intro h
    obtain ⟨v, d⟩ := p
    simp only at h
    subst h
    rw [P.sElt8_ev]
    exact P.ev8_mem v

theorem snd_of_mem_centralizer_w {p : Sc8} (h : P.sElt8 p ∈ Subgroup.centralizer {K.w}) :
    p.2 = 0 ∨ p.2 = (0, 0, 1) := by
  apply cent_w8
  apply P.sElt8_injective
  rw [P.sElt8_mul, P.sElt8_mul, P.sElt8_w8]
  exact (Subgroup.mem_centralizer_singleton_iff.mp h)

theorem comm_snd_zero : ∀ d e : Dc, (d = 0 ∨ d = (0, 0, 1)) → (e = 0 ∨ e = (0, 0, 1)) →
    dmul (dmul (dinv d) (dinv e)) (dmul d e) = 0 := by decide

theorem A_le_C : K.A ≤ P.C := by
  rw [K.hA, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact P.w_mem
  · rw [← P.ha2]; exact pow_mem P.a_mem 2
  · rw [← P.hb2]; exact pow_mem P.b_mem 2

theorem C_le_centralizer_A : P.C ≤ Subgroup.centralizer (K.A : Set G) := fun c hc =>
  Subgroup.mem_centralizer_iff.mpr fun a ha => P.comm (P.A_le_C ha) hc

theorem mem_A_of_mem_C {c : G} (hc : c ∈ P.C) (h4 : c ^ 4 = 1) : c ∈ K.A := by
  obtain ⟨v, rfl⟩ := P.exists_ev8 hc
  have h4' : 4 • v = 0 := P.ev8_injective (by rw [P.ev8_nsmul, h4, P.ev8_zero])
  obtain ⟨hj, hl⟩ := omega2_C8 v h4'
  have hx : P.a ^ v.2.1.val ∈ K.A := by
    rw [show v.2.1.val = 2 * (v.2.1.val / 2) by omega, pow_mul, P.ha2]
    exact pow_mem K.x_mem _
  have hy : P.b ^ v.2.2.val ∈ K.A := by
    rw [show v.2.2.val = 2 * (v.2.2.val / 2) by omega, pow_mul, P.hb2]
    exact pow_mem K.y_mem _
  exact mul_mem (mul_mem (pow_mem K.w_mem _) hx) hy

variable {S : Sylow 2 G} (hS : (S : Subgroup G) = P.Ssub8)
include hS

theorem mem_S_iff' {g : G} : g ∈ (S : Subgroup G) ↔ ∃ p, P.sElt8 p = g := by
  rw [hS]
  exact ⟨P.exists_sElt8, fun ⟨p, hp⟩ => hp ▸ P.sElt8_mem p⟩

theorem C_le_Q1 : P.C ≤ (S : Subgroup G) ⊓ Subgroup.centralizer {K.w} := fun c hc =>
  ⟨by rw [hS]; exact Subgroup.mem_sup_left hc,
    Subgroup.mem_centralizer_singleton_iff.mpr (P.comm hc P.w_mem)⟩

theorem u_mem_Q1 : K.u ∈ (S : Subgroup G) ⊓ Subgroup.centralizer {K.w} := by
  refine ⟨(P.mem_S_iff' hS).2 ⟨u8, P.sElt8_u8⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have h := K.hu_w
  calc K.u * K.w = K.u * (K.u⁻¹ * K.w * K.u) := by rw [h]
    _ = K.w * K.u := by group

theorem comm_mem_C {q₁ q₂ : G} (h₁ : q₁ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer {K.w})
    (h₂ : q₂ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer {K.w}) :
    q₁⁻¹ * q₂⁻¹ * q₁ * q₂ ∈ P.C := by
  obtain ⟨p₁, rfl⟩ := (P.mem_S_iff' hS).1 h₁.1
  obtain ⟨p₂, rfl⟩ := (P.mem_S_iff' hS).1 h₂.1
  have h : (P.sElt8 p₁)⁻¹ * (P.sElt8 p₂)⁻¹ * P.sElt8 p₁ * P.sElt8 p₂ =
      P.sElt8 (smul8 (smul8 (smul8 (sinv8 p₁) (sinv8 p₂)) p₁) p₂) := by
    rw [P.sElt8_mul, P.sElt8_mul, P.sElt8_mul, P.sElt8_sinv8, P.sElt8_sinv8]
  rw [h, P.mem_C_iff]
  have h2 : (smul8 (smul8 (smul8 (sinv8 p₁) (sinv8 p₂)) p₁) p₂).2 =
      dmul (dmul (dmul (dinv p₁.2) (dinv p₂.2)) p₁.2) p₂.2 := rfl
  rw [h2, dmul_assoc (dmul (dinv p₁.2) (dinv p₂.2)) p₁.2 p₂.2]
  exact comm_snd_zero _ _ (P.snd_of_mem_centralizer_w h₁.2) (P.snd_of_mem_centralizer_w h₂.2)

theorem conj_mem_C_of_mem_normalizer {g : G}
    (hg : g ∈ Subgroup.normalizer
      (((S : Subgroup G) ⊓ Subgroup.centralizer {K.w} : Subgroup G) : Set G))
    {c : G} (hc : c ∈ P.C) : g * c * g⁻¹ ∈ P.C := by
  set Q₁ := (S : Subgroup G) ⊓ Subgroup.centralizer {K.w}
  have hgQ : ∀ q ∈ Q₁, g * q * g⁻¹ ∈ Q₁ := fun q hq => (Subgroup.mem_normalizer_iff.mp hg q).mp hq
  have hgQ' : ∀ q ∈ Q₁, g⁻¹ * q * g ∈ Q₁ := fun q hq => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) q).mp hq
    simpa using this
  have hmem := hgQ c (P.C_le_Q1 hS hc)
  obtain ⟨p, hp⟩ := (P.mem_S_iff' hS).1 hmem.1
  rcases P.snd_of_mem_centralizer_w (hp ▸ hmem.2) with h0 | h1
  · rw [← hp, P.mem_C_iff]; exact h0
  · exfalso
    have ha : P.a ∈ Q₁ := P.C_le_Q1 hS P.a_mem
    have hu := P.u_mem_Q1 hS
    have hh₀ : P.sElt8 ainvb8 = P.a⁻¹ * K.u⁻¹ * P.a * K.u := by
      have ha8 : P.sElt8 ((0, 1, 0), (0, 0, 0)) = P.a := by
        rw [show ((0, 1, 0), (0, 0, 0)) = (((0, 1, 0) : Cc8), (0 : Dc)) from rfl, P.sElt8_ev,
          P.ev8_a]
      rw [ainvb8_comm, P.sElt8_mul, P.sElt8_mul, P.sElt8_mul, P.sElt8_sinv8, P.sElt8_sinv8,
        ha8, P.sElt8_u8]
      group
    have hκ : g⁻¹ * P.sElt8 ainvb8 * g ∈ P.C := by
      rw [hh₀, show g⁻¹ * (P.a⁻¹ * K.u⁻¹ * P.a * K.u) * g =
        (g⁻¹ * P.a * g)⁻¹ * (g⁻¹ * K.u * g)⁻¹ * (g⁻¹ * P.a * g) * (g⁻¹ * K.u * g) by group]
      exact P.comm_mem_C hS (hgQ' _ ha) (hgQ' _ hu)
    have hcomm : (g * c * g⁻¹) * P.sElt8 ainvb8 = P.sElt8 ainvb8 * (g * c * g⁻¹) := by
      have h := P.comm hc hκ
      calc (g * c * g⁻¹) * P.sElt8 ainvb8
          = g * (c * (g⁻¹ * P.sElt8 ainvb8 * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * P.sElt8 ainvb8 * g) * c) * g⁻¹ := by rw [h]
        _ = P.sElt8 ainvb8 * (g * c * g⁻¹) := by group
    rw [← hp] at hcomm
    obtain ⟨v, d⟩ := p
    simp only at h1
    subst h1
    apply cent_comm8 v
    apply P.sElt8_injective
    rw [P.sElt8_mul, P.sElt8_mul]
    exact hcomm

theorem mem_normalizer_A_of_mem_normalizer_Q1 (g : G)
    (hg : g ∈ Subgroup.normalizer
      (((S : Subgroup G) ⊓ Subgroup.centralizer {K.w} : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer (K.A : Set G) := by
  have key : ∀ k ∈ Subgroup.normalizer
      (((S : Subgroup G) ⊓ Subgroup.centralizer {K.w} : Subgroup G) : Set G),
      ∀ a ∈ K.A, k * a * k⁻¹ ∈ K.A := by
    intro k hk a ha
    refine P.mem_A_of_mem_C (P.conj_mem_C_of_mem_normalizer hS hk (P.A_le_C ha)) ?_
    rw [conj_pow, pow_four_of_mem_configA K ha, mul_one, mul_inv_cancel]
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨key g hg a, fun ha => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ ha
  rwa [show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group] at this

@[expose] noncomputable def coord8 (g : G) : Sc8 := Function.invFun P.sElt8 g

theorem sElt8_coord8 {g : G} (hg : g ∈ (S : Subgroup G)) : P.sElt8 (P.coord8 g) = g :=
  Function.invFun_eq ((P.mem_S_iff' hS).1 hg)

theorem card_Q1_le : Nat.card ((S : Subgroup G) ⊓ Subgroup.centralizer {K.w} : Subgroup G) ≤
    256 := by
  have hinj : Function.Injective (fun q : ((S : Subgroup G) ⊓ Subgroup.centralizer {K.w} :
      Subgroup G) => (⟨P.coord8 q, by
        have h := q.2.2
        rw [← P.sElt8_coord8 hS q.2.1] at h
        exact P.snd_of_mem_centralizer_w h⟩ : {p : Sc8 // p.2 = 0 ∨ p.2 = (0, 0, 1)})) := by
    intro q q' h
    apply Subtype.ext
    have h' := congrArg (fun p : {p : Sc8 // p.2 = 0 ∨ p.2 = (0, 0, 1)} => P.sElt8 p.1) h
    simp only [P.sElt8_coord8 hS q.2.1, P.sElt8_coord8 hS q'.2.1] at h'
    exact h'
  have h := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card (α := {p : Sc8 // p.2 = 0 ∨ p.2 = (0, 0, 1)}),
    card_snd_zero_or_u] at h

theorem relIndex_C_Q1_le : P.C.relIndex ((S : Subgroup G) ⊓ Subgroup.centralizer {K.w}) ≤ 2 := by
  have h := Subgroup.relIndex_mul_card (H := P.C)
    (K := (S : Subgroup G) ⊓ Subgroup.centralizer {K.w})
  rw [inf_of_le_left (P.C_le_Q1 hS), P.hCcard] at h
  have h2 := P.card_Q1_le hS
  by_contra hc
  push Not at hc
  have : 3 * 2 ^ 7 ≤ P.C.relIndex ((S : Subgroup G) ⊓ Subgroup.centralizer {K.w}) * 2 ^ 7 :=
    Nat.mul_le_mul_right _ hc
  omega

theorem no_elemAbelian_sixteen {F₁ : Subgroup G}
    (hF : F₁ ≤ (S : Subgroup G) ⊓ Subgroup.centralizer {K.w}) (hcard : Nat.card F₁ = 16)
    (hinv : ∀ f ∈ F₁, f * f = 1) (hcomm : ∀ f ∈ F₁, ∀ g ∈ F₁, f * g = g * f) : False := by
  classical
  have hne0 : P.C.relIndex ((S : Subgroup G) ⊓ Subgroup.centralizer {K.w}) ≠ 0 := by
    intro h0
    have h := Subgroup.relIndex_mul_card (H := P.C)
      (K := (S : Subgroup G) ⊓ Subgroup.centralizer {K.w})
    rw [h0, zero_mul] at h
    exact (Nat.card_pos (α := ((S : Subgroup G) ⊓ Subgroup.centralizer {K.w} : Subgroup G))).ne' h.symm
  have hidx : P.C.relIndex F₁ ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right hF hne0).trans (P.relIndex_C_Q1_le hS)
  have hmc := Subgroup.relIndex_mul_card (H := P.C) (K := F₁)
  rw [hcard] at hmc
  have h8 : 8 ≤ Nat.card (P.C ⊓ F₁ : Subgroup G) := by
    by_contra h
    push Not at h
    have : P.C.relIndex F₁ * Nat.card (P.C ⊓ F₁ : Subgroup G) ≤ 2 * 7 :=
      Nat.mul_le_mul hidx (by omega)
    omega
  have hS8 : ∀ f ∈ (P.C ⊓ F₁ : Subgroup G), f ∈ (S : Subgroup G) := fun f hf => (hF hf.2).1
  let ι : (P.C ⊓ F₁ : Subgroup G) → {v : Cc8 // v + v = 0} := fun f => ⟨(P.coord8 f).1, by
    have hf2 : smul8 (P.coord8 f) (P.coord8 f) = one8 := P.sElt8_injective (by
      rw [P.sElt8_mul, P.sElt8_coord8 hS (hS8 f f.2), P.sElt8_one8]; exact hinv _ f.2.2)
    have h0 : (P.coord8 f).2 = 0 := by
      rw [← P.mem_C_iff, P.sElt8_coord8 hS (hS8 f f.2)]; exact f.2.1
    have := congrArg Prod.fst hf2
    rw [smul8_self_fst _ h0] at this
    exact this⟩
  have hι : Function.Injective ι := by
    intro f f' h
    have h0 : ∀ g : (P.C ⊓ F₁ : Subgroup G), (P.coord8 g).2 = 0 := fun g => by
      rw [← P.mem_C_iff, P.sElt8_coord8 hS (hS8 g g.2)]; exact g.2.1
    have hc : P.coord8 f = P.coord8 f' :=
      Prod.ext (congrArg Subtype.val h) ((h0 f).trans (h0 f').symm)
    apply Subtype.ext
    rw [← P.sElt8_coord8 hS (hS8 f f.2), ← P.sElt8_coord8 hS (hS8 f' f'.2), hc]
  have hcardΩ : Nat.card {v : Cc8 // v + v = 0} = 8 := by
    rw [Nat.card_eq_fintype_card]; decide
  have hle := Nat.card_le_card_of_injective ι hι
  rw [hcardΩ] at hle
  have hbij : Function.Bijective ι :=
    hι.bijective_of_nat_card_le (by rw [hcardΩ]; exact h8)
  obtain ⟨f₀, hf₀⟩ := hbij.2 ⟨(0, 4, 0), by decide⟩
  have hf₀c : P.coord8 f₀ = a4_8 := by
    have h1 := congrArg Subtype.val hf₀
    have h0 : (P.coord8 f₀).2 = 0 := by
      rw [← P.mem_C_iff, P.sElt8_coord8 hS (hS8 f₀ f₀.2)]; exact f₀.2.1
    exact Prod.ext h1 h0
  have ha4 : P.sElt8 a4_8 ∈ F₁ := by
    rw [← hf₀c, P.sElt8_coord8 hS (hS8 f₀ f₀.2)]; exact f₀.2.2
  obtain ⟨m, hmF, hmC⟩ : ∃ m ∈ F₁, m ∉ P.C := by
    by_contra h
    push Not at h
    have : P.C ⊓ F₁ = F₁ := inf_eq_right.mpr h
    rw [this, hcard] at hle
    omega
  have hmS := (hF hmF).1
  have hm1 : (P.coord8 m).2 = (0, 0, 1) := by
    rcases P.snd_of_mem_centralizer_w (by rw [P.sElt8_coord8 hS hmS]; exact (hF hmF).2) with
      h | h
    · exact absurd (by rw [← P.sElt8_coord8 hS hmS, P.mem_C_iff]; exact h) hmC
    · exact h
  have hc := hcomm m hmF _ ha4
  rw [← P.sElt8_coord8 hS hmS, ← P.sElt8_mul, ← P.sElt8_mul] at hc
  have hc' := P.sElt8_injective hc
  have hm' : P.coord8 m = ((P.coord8 m).1, (0, 0, 1)) := Prod.ext rfl hm1
  rw [hm'] at hc'
  exact cent_a4_8 _ hc'

end ShapeII

variable {G : Type*} [Group G] [Finite G]

theorem arch76Lemma3_not_shapeII (K : Config G) (P : ShapeII K)
    (hfusE : ∀ e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}, e ≠ 1 →
      IsConj e ((K.x * K.y) ^ 2))
    (huw : IsConj K.u K.w) (hwu : IsConj (K.w * K.u) (K.x * K.y * K.uv))
    (hAnn1 : ¬ IsConj K.w ((K.x * K.y) ^ 2)) (S : Sylow 2 G)
    (hS : (S : Subgroup G) = P.C ⊔ Subgroup.closure {K.uv, K.t, K.u}) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : (S : Subgroup G) = P.Ssub8 := hS
  set z := (K.x * K.y) ^ 2 with hzdef
  have hz : P.sElt8 z8 = z := P.sElt8_z8
  have hzS : (S : Subgroup G) ≤ Subgroup.centralizer {z} := by
    intro g hg
    obtain ⟨p, rfl⟩ := (P.mem_S_iff' hS').1 hg
    rw [Subgroup.mem_centralizer_singleton_iff, ← hz]
    exact P.sElt8_comm (z8_central p)
  have hfact : ∀ r' ∈ (S : Subgroup G), r' * r' = 1 → r' ≠ 1 → r' ≠ z →
      ∃ q ∈ (S : Subgroup G), q⁻¹ * r' * q = r' * z := by
    intro r' hr' h2 h1 hne
    obtain ⟨p, rfl⟩ := (P.mem_S_iff' hS').1 hr'
    have hp2 : smul8 p p = one8 := P.sElt8_injective (by rw [P.sElt8_mul, P.sElt8_one8, h2])
    have hp1 : p ≠ one8 := fun h => h1 (by rw [h, P.sElt8_one8])
    have hpz : p ≠ z8 := fun h => hne (by rw [h, hz])
    have hI : isInv8 p = true := by
      simp only [isInv8, hp2, beq_self_eq_true, Bool.true_and, bne_iff_ne, ne_eq]
      exact hp1
    have hc := tabZ8_complete p
    rw [hI] at hc
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hc
    rcases hc with hc | ⟨e, he, hep⟩
    · exact absurd hc hpz
    subst hep
    refine ⟨P.sElt8 e.2, by rw [hS']; exact P.sElt8_mem _, ?_⟩
    have hchk := List.all_eq_true.1 tabZ8Check_eq e he
    simp only [beq_iff_eq] at hchk
    have h := congrArg P.sElt8 hchk
    rw [P.sElt8_mul, P.sElt8_mul, P.sElt8_mul, hz] at h
    rw [mul_assoc, h]; group
  have huv1 : K.uv ≠ 1 := by rw [← tElt_gen_uv K]; exact tElt_ne_one K (by decide)
  have hxyuv : IsConj K.uv (K.x * K.y * K.uv) := by
    refine isConj_of_conj (P.sElt8 g0_8) ?_
    have h := congrArg P.sElt8 uv_conj_xyuv8
    rw [P.sElt8_mul, P.sElt8_mul, P.sElt8_uv8, P.sElt8_xyuv8] at h
    rw [mul_assoc, h]; group
  have hvz : IsConj (K.w * K.u) z :=
    hwu.trans (hxyuv.symm.trans (hfusE _ (uv_mem_closureE K) huv1))
  obtain ⟨hr2, hrv, hrq, hqta, hrne, hr1⟩ := r0_facts
  set r := P.sElt8 r0_8 with hrdef
  have hrS : r ∈ (S : Subgroup G) := by rw [hS']; exact P.sElt8_mem _
  have hvS : K.w * K.u ∈ (S : Subgroup G) := by rw [hS', ← P.sElt8_wu8]; exact P.sElt8_mem _
  have hrv' : r * (K.w * K.u) = (K.w * K.u) * r := by
    rw [← P.sElt8_wu8]; exact P.sElt8_comm hrv
  have hr2' : r * r = 1 := by rw [hrdef, ← P.sElt8_mul, hr2, P.sElt8_one8]
  have hr1' : r ≠ 1 := fun h => hr1 (P.sElt8_injective (h.trans P.sElt8_one8.symm))
  have hne' : r ≠ K.w * K.u := fun h => hrne (P.sElt8_injective (h.trans P.sElt8_wu8.symm))
  have h6 := isConj_mul_of_isConj_central S hzS hfact hvz hrS hvS hrv' hr2' hr1' hne'
  have hq : r * (K.w * K.u) = P.sElt8 q0_8 := by rw [← P.sElt8_wu8, ← P.sElt8_mul, hrq]
  have hqu : IsConj (P.sElt8 q0_8) K.u := by
    refine isConj_of_conj (P.sElt8 ta8) ?_
    have h := congrArg P.sElt8 hqta
    rw [P.sElt8_mul, P.sElt8_mul, P.sElt8_u8] at h
    rw [mul_assoc, h]; group
  rw [hq] at h6
  have hrw : IsConj r K.w := (h6.trans hqu).trans huw
  obtain ⟨c, hc⟩ := isConj_iff.mp hrw
  have hconjcomm : ∀ x f g : G, f * g = g * f →
      (x * f * x⁻¹) * (x * g * x⁻¹) = (x * g * x⁻¹) * (x * f * x⁻¹) := by
    intro x f g hfg
    calc (x * f * x⁻¹) * (x * g * x⁻¹) = x * (f * g) * x⁻¹ := by group
      _ = x * (g * f) * x⁻¹ := by rw [hfg]
      _ = (x * g * x⁻¹) * (x * f * x⁻¹) := by group
  set F' := P.Fsub.map (MulAut.conj c).toMonoidHom with hF'
  have hF'w : F' ≤ Subgroup.centralizer {K.w} := by
    rintro _ ⟨f, hf, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hc]
    exact hconjcomm c f r (P.Fsub_comm hf P.r0_mem_Fsub)
  have hF'card : Nat.card F' = 16 := by rw [hF', card_map_conj, P.card_Fsub]
  have hF'p : IsPGroup 2 F' := IsPGroup.of_card (n := 4) (by rw [hF'card]; norm_num)
  have hTS : Tsub K ≤ (S : Subgroup G) := by
    rw [hS']; exact sup_le_sup_right P.A_le_C _
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (K.A : Set G) := by
    rw [hS']
    refine sup_le (fun c hc => Subgroup.centralizer_le_normalizer _ (P.C_le_centralizer_A hc)) ?_
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    exacts [uv_mem_normalizer_A K, t_mem_normalizer_A K, u_mem_normalizer_A K]
  have hmax : ∀ {Q : Subgroup G}, IsPGroup 2 Q → Q ≤ Subgroup.centralizer {K.w} →
      (S : Subgroup G) ⊓ Subgroup.centralizer {K.w} ≤ Q →
        Q = (S : Subgroup G) ⊓ Subgroup.centralizer {K.w} := fun hQ hQw hQQ =>
    eq_of_le_centralizer_w K hfusE hAnn1 S hTS hSN
      (P.mem_normalizer_A_of_mem_normalizer_Q1 hS') hQ hQw hQQ
  have hQ1p : IsPGroup 2 ((S : Subgroup G) ⊓ Subgroup.centralizer {K.w} : Subgroup G) :=
    S.isPGroup'.to_le inf_le_left
  obtain ⟨k, -, hkF⟩ := exists_conj_le_of_maximal inf_le_right hQ1p hmax hF'p hF'w
  refine P.no_elemAbelian_sixteen hS' (F₁ := F'.map (MulAut.conj k⁻¹).toMonoidHom) ?_ ?_ ?_ ?_
  · rintro _ ⟨f, hf, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hkF f hf
  · rw [card_map_conj, hF'card]
  · rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc k⁻¹ * (c * f * c⁻¹) * k⁻¹⁻¹ * (k⁻¹ * (c * f * c⁻¹) * k⁻¹⁻¹)
        = k⁻¹ * c * (f * f) * c⁻¹ * k := by group
      _ = 1 := by rw [P.Fsub_inv hf]; group
  · rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩ _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hconjcomm k⁻¹ _ _ (hconjcomm c f g (P.Fsub_comm hf hg))

end CFSG.CGT.Stroth76
