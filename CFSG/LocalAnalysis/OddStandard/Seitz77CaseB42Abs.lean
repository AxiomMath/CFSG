module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB41Mod

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.ABGLocalTools
open scoped commutatorElement

section Abs42

variable {G : Type} [Group G] [Finite G]

structure Odd2 (M₁ M₂ : Subgroup G) : Prop where
  norm₁ : ∀ x ∈ M₁ ⊔ M₂, ∀ m ∈ M₁, x * m * x⁻¹ ∈ M₁
  norm₂ : ∀ x ∈ M₁ ⊔ M₂, ∀ m ∈ M₂, x * m * x⁻¹ ∈ M₂
  odd_inf : Odd (Nat.card ↥(M₁ ⊓ M₂))

theorem card_sup_mul_card_inf {M₁ M₂ : Subgroup G} (h : ∀ x ∈ M₁, ∀ m ∈ M₂, x * m * x⁻¹ ∈ M₂) :
    Nat.card ↥(M₁ ⊔ M₂) * Nat.card ↥(M₁ ⊓ M₂) = Nat.card ↥M₁ * Nat.card ↥M₂ := by
  have h1Y : M₁ ≤ M₁ ⊔ M₂ := le_sup_left
  have h2Y : M₂ ≤ M₁ ⊔ M₂ := le_sup_right
  have hn : (M₂.subgroupOf (M₁ ⊔ M₂)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer h2Y]
    refine sup_le (fun x hx => Subgroup.mem_normalizer_fintype fun n hn => h x hx n hn) ?_
    exact fun x hx => Subgroup.mem_normalizer_fintype fun n hn =>
      M₂.mul_mem (M₂.mul_mem hx hn) (M₂.inv_mem hx)
  have htop : M₁.subgroupOf (M₁ ⊔ M₂) ⊔ M₂.subgroupOf (M₁ ⊔ M₂) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup h1Y h2Y, Subgroup.subgroupOf_self]
  have h1 : (M₂.subgroupOf (M₁ ⊔ M₂)).relIndex
        (M₁.subgroupOf (M₁ ⊔ M₂) ⊔ M₂.subgroupOf (M₁ ⊔ M₂)) =
      (M₂.subgroupOf (M₁ ⊔ M₂)).relIndex (M₁.subgroupOf (M₁ ⊔ M₂)) :=
    Subgroup.relIndex_sup_right _ _
  rw [htop, Subgroup.relIndex_top_right] at h1
  have h2 := Subgroup.relIndex_mul_card (M₂.subgroupOf (M₁ ⊔ M₂)) (M₁.subgroupOf (M₁ ⊔ M₂))
  have hc₁ : Nat.card ↥(M₁.subgroupOf (M₁ ⊔ M₂)) = Nat.card ↥M₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h1Y).toEquiv
  have hc₂ : Nat.card ↥(M₂.subgroupOf (M₁ ⊔ M₂)) = Nat.card ↥M₂ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h2Y).toEquiv
  have hinf : M₂.subgroupOf (M₁ ⊔ M₂) ⊓ M₁.subgroupOf (M₁ ⊔ M₂) =
      (M₂ ⊓ M₁).subgroupOf (M₁ ⊔ M₂) := (Subgroup.comap_inf _ _ _).symm
  have hcI : Nat.card ↥((M₂ ⊓ M₁).subgroupOf (M₁ ⊔ M₂)) = Nat.card ↥(M₂ ⊓ M₁) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans h2Y)).toEquiv
  rw [hinf, hcI, hc₁, inf_comm] at h2
  have h3 := Subgroup.index_mul_card (H := M₂.subgroupOf (M₁ ⊔ M₂))
  rw [hc₂] at h3
  rw [← h3, h1, ← h2]
  ring

namespace Odd2

variable {M₁ M₂ S : Subgroup G} (h : Odd2 M₁ M₂)

include h

theorem inf_eq_bot (hS : IsPGroup 2 S) : S ⊓ (M₁ ⊓ M₂) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥(S ⊓ (M₁ ⊓ M₂)) := hS.to_inf_left
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  rcases n with _ | n
  · exact Subgroup.eq_bot_of_card_eq _ (by simpa using hn)
  · exfalso
    have hd : Nat.card ↥(S ⊓ (M₁ ⊓ M₂)) ∣ Nat.card ↥(M₁ ⊓ M₂) :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [hn] at hd
    exact h.odd_inf.not_two_dvd_nat ((dvd_pow_self 2 n.succ_ne_zero).trans hd)

omit [Finite G] in
theorem comm_mem {a b : G} (ha : a ∈ M₁) (hb : b ∈ M₂) : ⁅a, b⁆ ∈ M₁ ⊓ M₂ := by
  have h1 : b * a⁻¹ * b⁻¹ ∈ M₁ := h.norm₁ b (mem_sup_right hb) a⁻¹ (M₁.inv_mem ha)
  have h2 : a * b * a⁻¹ ∈ M₂ := h.norm₂ a (mem_sup_left ha) b hb
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    simpa only [mul_assoc] using M₁.mul_mem ha h1
  · rw [commutatorElement_def]
    exact M₂.mul_mem h2 (M₂.inv_mem hb)

theorem comm (hS : IsPGroup 2 S) {a b : G} (ha : a ∈ S ⊓ M₁) (hb : b ∈ S ⊓ M₂) :
    a * b = b * a := by
  have h1 : ⁅a, b⁆ ∈ S ⊓ (M₁ ⊓ M₂) :=
    ⟨S.mul_mem (S.mul_mem (S.mul_mem ha.1 hb.1) (S.inv_mem ha.1)) (S.inv_mem hb.1),
      h.comm_mem ha.2 hb.2⟩
  rw [h.inf_eq_bot hS] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)

theorem inf_inf_eq_bot (hS : IsPGroup 2 S) : (S ⊓ M₁) ⊓ (S ⊓ M₂) = ⊥ := by
  refine eq_bot_iff.mpr ?_
  rw [← h.inf_eq_bot hS]
  exact fun x hx => ⟨hx.1.1, hx.1.2, hx.2.2⟩

theorem sylow_inf (hS : IsSylowOf 2 S (M₁ ⊔ M₂)) :
    IsSylowOf 2 (S ⊓ M₁) M₁ ∧ IsSylowOf 2 (S ⊓ M₂) M₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hS.inf_of_le_normalizer le_sup_left ?_, hS.inf_of_le_normalizer le_sup_right ?_⟩
  · exact fun x hx => Subgroup.mem_normalizer_fintype fun n hn => h.norm₁ x hx n hn
  · exact fun x hx => Subgroup.mem_normalizer_fintype fun n hn => h.norm₂ x hx n hn

private theorem card_sylow_aux (hS : IsSylowOf 2 S (M₁ ⊔ M₂)) :
    Nat.card ↥S = Nat.card ↥(S ⊓ M₁) * Nat.card ↥(S ⊓ M₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hS₁, hS₂⟩ := h.sylow_inf hS
  rw [hS.card_eq, hS₁.card_eq, hS₂.card_eq, ← pow_add]
  congr 1
  have hcard := card_sup_mul_card_inf (fun x hx m hm => h.norm₂ x (mem_sup_left hx) m hm)
  have hodd : (Nat.card ↥(M₁ ⊓ M₂)).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd h.odd_inf.not_two_dvd_nat
  have hne₁ : Nat.card ↥(M₁ ⊔ M₂) ≠ 0 := Nat.card_pos.ne'
  have hne₂ : Nat.card ↥(M₁ ⊓ M₂) ≠ 0 := Nat.card_pos.ne'
  have hne₃ : Nat.card ↥M₁ ≠ 0 := Nat.card_pos.ne'
  have hne₄ : Nat.card ↥M₂ ≠ 0 := Nat.card_pos.ne'
  have hfac := congrArg (fun n => n.factorization 2) hcard
  simp only [Nat.factorization_mul hne₁ hne₂, Nat.factorization_mul hne₃ hne₄,
    Finsupp.add_apply, hodd, add_zero] at hfac
  exact hfac

theorem sylow_eq_sup (hS : IsSylowOf 2 S (M₁ ⊔ M₂)) : S = (S ⊓ M₁) ⊔ (S ⊓ M₂) := by
  have hp := hS.isPGroup
  have hle : (S ⊓ M₁) ⊔ (S ⊓ M₂) ≤ S := sup_le inf_le_left inf_le_left
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have e := supEquivProd (S ⊓ M₁) (S ⊓ M₂) (fun x hx y hy => h.comm hp hx hy)
    (disjoint_iff.mpr (h.inf_inf_eq_bot hp))
  rw [h.card_sylow_aux hS, Nat.card_congr e.toEquiv, Nat.card_prod]

end Odd2

theorem exists_sylow_invariant {L Q V : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQL : ∀ q ∈ Q, ∀ l ∈ L, q * l * q⁻¹ ∈ L) (hVQ : V ≤ Q) (hVL : V ≤ L) :
    ∃ S : Subgroup G, IsSylowOf 2 S L ∧ V ≤ S ∧ ∀ q ∈ Q, ∀ s ∈ S, q * s * q⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLY : L ≤ L ⊔ Q := le_sup_left
  have hQY : Q ≤ L ⊔ Q := le_sup_right
  obtain ⟨R, hR⟩ := (hQ.comap_subtype : IsPGroup 2 ↥(Q.subgroupOf (L ⊔ Q))).exists_le_sylow
  have hTsyl : IsSylowOf 2 ((R : Subgroup ↥(L ⊔ Q)).map (L ⊔ Q).subtype) (L ⊔ Q) := ⟨R, rfl⟩
  have hQT : Q ≤ (R : Subgroup ↥(L ⊔ Q)).map (L ⊔ Q).subtype := fun x hx =>
    ⟨⟨x, hQY hx⟩, hR (mem_subgroupOf.mpr hx), rfl⟩
  generalize (R : Subgroup ↥(L ⊔ Q)).map (L ⊔ Q).subtype = T at hTsyl hQT
  have hYN : L ⊔ Q ≤ normalizer (L : Set G) := by
    refine sup_le (fun x hx => Subgroup.mem_normalizer_fintype fun n hn =>
      L.mul_mem (L.mul_mem hx hn) (L.inv_mem hx)) ?_
    exact fun x hx => Subgroup.mem_normalizer_fintype fun n hn => hQL x hx n hn
  refine ⟨T ⊓ L, hTsyl.inf_of_le_normalizer hLY hYN, le_inf (hVQ.trans hQT) hVL, ?_⟩
  intro q hq s hs
  exact ⟨T.mul_mem (T.mul_mem (hQT hq) hs.1) (T.inv_mem (hQT hq)), hQL q hq s hs.2⟩

structure Prod2 (M₁ M₂ S V : Subgroup G) (t : G) : Prop where
  odd2 : Odd2 M₁ M₂
  t_sq : t * t = 1
  swap₁ : ∀ x ∈ M₁, t * x * t⁻¹ ∈ M₂
  swap₂ : ∀ x ∈ M₂, t * x * t⁻¹ ∈ M₁
  sylow : IsSylowOf 2 S (M₁ ⊔ M₂)
  inv : ∀ s ∈ S, t * s * t⁻¹ ∈ S
  V_le : V ≤ S
  V_comm : ∀ v ∈ V, v * t = t * v
  card_V : Nat.card ↥V = 64
  card₁ : ∀ T : Subgroup G, IsSylowOf 2 T M₁ → Nat.card ↥T = 64

namespace Prod2

variable {M₁ M₂ S V : Subgroup G} {t : G} (P : Prod2 M₁ M₂ S V t)

include P

theorem sylow₁ : IsSylowOf 2 (S ⊓ M₁) M₁ := (P.odd2.sylow_inf P.sylow).1

theorem sylow₂ : IsSylowOf 2 (S ⊓ M₂) M₂ := (P.odd2.sylow_inf P.sylow).2

theorem card_A : Nat.card ↥(S ⊓ M₁) = 64 := P.card₁ _ P.sylow₁

theorem comm_AB {a b : G} (ha : a ∈ S ⊓ M₁) (hb : b ∈ S ⊓ M₂) : a * b = b * a :=
  P.odd2.comm P.sylow.isPGroup ha hb

theorem inf_AB : (S ⊓ M₁) ⊓ (S ⊓ M₂) = ⊥ := P.odd2.inf_inf_eq_bot P.sylow.isPGroup

theorem S_eq : S = (S ⊓ M₁) ⊔ (S ⊓ M₂) := P.odd2.sylow_eq_sup P.sylow

omit [Finite G] in
theorem swap_A {x : G} (hx : x ∈ S ⊓ M₁) : t * x * t⁻¹ ∈ S ⊓ M₂ :=
  ⟨P.inv x hx.1, P.swap₁ x hx.2⟩

omit [Finite G] in
theorem swap_B {x : G} (hx : x ∈ S ⊓ M₂) : t * x * t⁻¹ ∈ S ⊓ M₁ :=
  ⟨P.inv x hx.1, P.swap₂ x hx.2⟩

omit [Finite G] in
theorem conj_conj (x : G) : t * (t * x * t⁻¹) * t⁻¹ = x := by
  have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right P.t_sq
  rw [ht]
  calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
    _ = x := by rw [P.t_sq]; group

theorem exists_diag {v : G} (hv : v ∈ S) (hvt : v * t = t * v) :
    ∃ a ∈ S ⊓ M₁, v = a * (t * a * t⁻¹) := by
  have hmem : v ∈ (S ⊓ M₁) ⊔ (S ⊓ M₂) := P.S_eq ▸ hv
  obtain ⟨a, ha, b, hb, hab⟩ :=
    mem_sup_of_forall_comm (fun x hx y hy => P.comm_AB hx hy) hmem
  have ha' : t * a * t⁻¹ ∈ S ⊓ M₂ := P.swap_A ha
  have hb' : t * b * t⁻¹ ∈ S ⊓ M₁ := P.swap_B hb
  have hvt' : t * v * t⁻¹ = v := by
    calc t * v * t⁻¹ = v * t * t⁻¹ := by rw [hvt]
      _ = v := by group
  have h1 : (t * a * t⁻¹) * (t * b * t⁻¹) = a * b := by
    calc (t * a * t⁻¹) * (t * b * t⁻¹) = t * (a * b) * t⁻¹ := by group
      _ = a * b := by rw [← hab]; exact hvt'
  have h2 : (t * b * t⁻¹) * (t * a * t⁻¹) = a * b := by
    rw [P.comm_AB hb' ha']
    exact h1
  have h3 : (t * b * t⁻¹)⁻¹ * a = (t * a * t⁻¹) * b⁻¹ := by
    calc (t * b * t⁻¹)⁻¹ * a = (t * b * t⁻¹)⁻¹ * (a * b) * b⁻¹ := by group
      _ = (t * b * t⁻¹)⁻¹ * ((t * b * t⁻¹) * (t * a * t⁻¹)) * b⁻¹ := by rw [← h2]
      _ = (t * a * t⁻¹) * b⁻¹ := by group
  have hmemAB : (t * b * t⁻¹)⁻¹ * a ∈ (S ⊓ M₁) ⊓ (S ⊓ M₂) := by
    refine ⟨(S ⊓ M₁).mul_mem ((S ⊓ M₁).inv_mem hb') ha, ?_⟩
    rw [h3]
    exact (S ⊓ M₂).mul_mem ha' ((S ⊓ M₂).inv_mem hb)
  rw [P.inf_AB, Subgroup.mem_bot] at hmemAB
  have hba : t * b * t⁻¹ = a := inv_mul_eq_one.mp hmemAB
  have hab' : t * a * t⁻¹ = b := by
    rw [← hba, P.conj_conj]
  refine ⟨a, ha, ?_⟩
  rw [hab']
  exact hab

theorem diag_mem {a : G} (ha : a ∈ S ⊓ M₁) :
    a * (t * a * t⁻¹) ∈ S ∧ (a * (t * a * t⁻¹)) * t = t * (a * (t * a * t⁻¹)) := by
  refine ⟨S.mul_mem ha.1 (P.inv a ha.1), ?_⟩
  have hc : a * (t * a * t⁻¹) = (t * a * t⁻¹) * a := P.comm_AB ha (P.swap_A ha)
  have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right P.t_sq
  calc a * (t * a * t⁻¹) * t = (t * a * t⁻¹) * a * t := by rw [hc]
    _ = t * (a * (t * a * t⁻¹)) := by rw [ht]; group

theorem V_eq : V = S ⊓ centralizer ({t} : Set G) := by
  have hle : V ≤ S ⊓ centralizer ({t} : Set G) :=
    le_inf P.V_le fun v hv => mem_centralizer_singleton_iff.mpr (P.V_comm v hv)
  have hex : ∀ s : ↥(S ⊓ centralizer ({t} : Set G)), ∃ a : ↥(S ⊓ M₁),
      (s : G) = (a : G) * (t * a * t⁻¹) := fun s => by
    obtain ⟨a, ha, h⟩ := P.exists_diag s.2.1 (mem_centralizer_singleton_iff.mp s.2.2)
    exact ⟨⟨a, ha⟩, h⟩
  choose g hg using hex
  have hinj : Function.Injective g := fun s s' h => Subtype.ext (by rw [hg s, hg s', h])
  have hcard : Nat.card ↥(S ⊓ centralizer ({t} : Set G)) ≤ Nat.card ↥V := by
    rw [P.card_V, ← P.card_A]
    exact Nat.card_le_card_of_injective g hinj
  exact Subgroup.eq_of_le_of_card_ge hle hcard

theorem diag_mem_V {a : G} (ha : a ∈ S ⊓ M₁) : a * (t * a * t⁻¹) ∈ V := by
  rw [P.V_eq]
  exact ⟨(P.diag_mem ha).1, mem_centralizer_singleton_iff.mpr (P.diag_mem ha).2⟩

theorem exists_diag_V {v : G} (hv : v ∈ V) : ∃ a ∈ S ⊓ M₁, v = a * (t * a * t⁻¹) :=
  P.exists_diag (P.V_le hv) (P.V_comm v hv)

@[expose] noncomputable def deltaHom : ↥(S ⊓ M₁) →* ↥V :=
  MonoidHom.mk' (fun a : ↥(S ⊓ M₁) => (⟨(a : G) * (t * a * t⁻¹), P.diag_mem_V a.2⟩ : ↥V))
    (fun a a' => by
      refine Subtype.ext ?_
      have hc : (t * (a : G) * t⁻¹) * (a' : G) = (a' : G) * (t * (a : G) * t⁻¹) :=
        (P.comm_AB a'.2 (P.swap_A a.2)).symm
      show (a : G) * (a' : G) * (t * ((a : G) * (a' : G)) * t⁻¹) =
        (a : G) * (t * (a : G) * t⁻¹) * ((a' : G) * (t * (a' : G) * t⁻¹))
      calc (a : G) * (a' : G) * (t * ((a : G) * (a' : G)) * t⁻¹)
          = (a : G) * ((a' : G) * (t * (a : G) * t⁻¹)) * (t * (a' : G) * t⁻¹) := by group
        _ = (a : G) * ((t * (a : G) * t⁻¹) * (a' : G)) * (t * (a' : G) * t⁻¹) := by rw [hc]
        _ = _ := by group)

theorem deltaHom_bijective : Function.Bijective P.deltaHom :=
  ⟨fun a a' h => by
    have h1 : (a : G) * (t * (a : G) * t⁻¹) = (a' : G) * (t * (a' : G) * t⁻¹) :=
      congrArg Subtype.val h
    have hm : (a' : G)⁻¹ * (a : G) = (t * (a' : G) * t⁻¹) * (t * (a : G) * t⁻¹)⁻¹ := by
      calc (a' : G)⁻¹ * (a : G) = (a' : G)⁻¹ * ((a : G) * (t * (a : G) * t⁻¹)) *
            (t * (a : G) * t⁻¹)⁻¹ := by group
        _ = (a' : G)⁻¹ * ((a' : G) * (t * (a' : G) * t⁻¹)) * (t * (a : G) * t⁻¹)⁻¹ := by
            rw [h1]
        _ = _ := by group
    have hmem : (a' : G)⁻¹ * (a : G) ∈ (S ⊓ M₁) ⊓ (S ⊓ M₂) := by
      refine ⟨(S ⊓ M₁).mul_mem ((S ⊓ M₁).inv_mem a'.2) a.2, ?_⟩
      rw [hm]
      exact (S ⊓ M₂).mul_mem (P.swap_A a'.2) ((S ⊓ M₂).inv_mem (P.swap_A a.2))
    rw [P.inf_AB, Subgroup.mem_bot] at hmem
    exact Subtype.ext (inv_mul_eq_one.mp hmem).symm,
  fun v => by
    obtain ⟨a, ha, h⟩ := P.exists_diag_V v.2
    exact ⟨⟨a, ha⟩, Subtype.ext h.symm⟩⟩

@[expose] noncomputable def deltaEquiv : ↥(S ⊓ M₁) ≃* ↥V :=
  MulEquiv.ofBijective P.deltaHom P.deltaHom_bijective

end Prod2

end Abs42

end CFSG.OddStandard.Seitz77
