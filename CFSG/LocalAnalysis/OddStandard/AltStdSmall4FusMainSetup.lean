module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4FusDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4CentCard
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4N0StructBase
public import CFSG.LocalAnalysis.OddStandard.AltStdSmallFusion

public section

namespace CFSG.OddStandard.AltStdSmall4.Fus.Main

open Subgroup Equiv AltStdCycTwo
open scoped commutatorElement

section Group

variable {G : Type} [Group G]

theorem mem_sup_zpowers_iff_of_mul_self {P : Subgroup G} {u : G} (hu : u * u = 1)
    (hn : ∀ p ∈ P, u * p * u⁻¹ ∈ P) {x : G} : x ∈ P ⊔ zpowers u ↔ x ∈ P ∨ x * u ∈ P := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  let K : Subgroup G :=
    { carrier := {x | x ∈ P ∨ x * u ∈ P}
      one_mem' := Or.inl P.one_mem
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (P.mul_mem hx hy)
        · exact Or.inr (by rw [mul_assoc]; exact P.mul_mem hx hy)
        · right
          have h1 : u * y * u⁻¹ ∈ P := hn y hy
          have : x * y * u = (x * u) * (u * y * u⁻¹) := by
            rw [huinv, show x * u * (u * y * u) = x * (u * u) * y * u by group, hu, mul_one]
          rw [this]
          exact P.mul_mem hx h1
        · left
          have h1 : u * (y * u) * u⁻¹ ∈ P := hn _ hy
          have : x * y = (x * u) * (u * (y * u) * u⁻¹) := by
            rw [huinv]
            calc x * y = x * (u * u) * y * (u * u) := by rw [hu]; group
              _ = x * u * (u * (y * u) * u) := by group
          rw [this]
          exact P.mul_mem hx h1
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (P.inv_mem hx)
        · right
          have h1 := hn _ (P.inv_mem hx)
          have : x⁻¹ * u = u * (x * u)⁻¹ * u⁻¹ := by rw [huinv]; group
          rw [this]
          exact h1 }
  have hK : P ⊔ zpowers u = K := by
    apply le_antisymm
    · refine sup_le (fun x hx => Or.inl hx) ?_
      rw [zpowers_le]
      right
      rw [hu]
      exact P.one_mem
    · rintro x (hx | hx)
      · exact mem_sup_left hx
      · have : x = (x * u) * u := by rw [mul_assoc, hu, mul_one]
        rw [this]
        exact mul_mem (mem_sup_left hx) (mem_sup_right (mem_zpowers u))
  rw [hK]
  rfl

theorem card_sup_zpowers_of_mul_self [Finite G] {P : Subgroup G} {u : G} (hu : u * u = 1)
    (hn : ∀ p ∈ P, u * p * u⁻¹ ∈ P) (huP : u ∉ P) :
    Nat.card ↥(P ⊔ zpowers u) = 2 * Nat.card P := by
  have hdisj : Disjoint (P : Set G) ((fun x => x * u) '' (P : Set G)) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨y, hy, rfl⟩
    have : u = y⁻¹ * (y * u) := by group
    exact huP (this ▸ P.mul_mem (P.inv_mem hy) hx)
  have hunion : ((P ⊔ zpowers u : Subgroup G) : Set G) =
      (P : Set G) ∪ (fun x => x * u) '' (P : Set G) := by
    ext x
    rw [SetLike.mem_coe, mem_sup_zpowers_iff_of_mul_self hu hn, Set.mem_union, SetLike.mem_coe]
    refine or_congr Iff.rfl ⟨fun h => ⟨x * u, h, by
      show x * u * u = x
      rw [mul_assoc, hu, mul_one]⟩, ?_⟩
    rintro ⟨y, hy, rfl⟩
    show y * u * u ∈ P
    rw [mul_assoc, hu, mul_one]
    exact hy
  have hinj : Set.InjOn (fun x => x * u) (P : Set G) := fun x _ y _ h => mul_right_cancel h
  have h1 : Nat.card ↥(P ⊔ zpowers u) = ((P ⊔ zpowers u : Subgroup G) : Set G).ncard :=
    Nat.card_coe_set_eq _
  have h2 : Nat.card ↥P = (P : Set G).ncard := Nat.card_coe_set_eq _
  rw [h1, hunion, Set.ncard_union_eq hdisj, hinj.ncard_image, h2]
  ring

theorem self_mem_centralizer_singleton (z : G) : z ∈ centralizer ({z} : Set G) :=
  mem_centralizer_singleton_iff.2 rfl

end Group

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G}

section Basic

variable (c : Config G L Q n θ z)
include c

theorem z_mul_self : z * z = 1 := c.ot.cyc.mul_self

theorem z_ne_one : z ≠ 1 := by
  intro h
  have h2 := c.ot.cyc.order
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem z_mem_centralizer_L : z ∈ centralizer (L : Set G) := c.ot.cyc.le c.ot.cyc.mem

theorem L_le_cent : L ≤ centralizer ({z} : Set G) := le_cent_single c.ot.std c.ot.cyc

theorem rhoC_coe (l : L) (hl : (l : G) ∈ centralizer ({z} : Set G)) :
    rhoC c ⟨l, hl⟩ = ((θ l : alternatingGroup (Fin n)) : Perm (Fin n)) := by
  rw [rhoC_apply, AltStdBal.rho_of_mem]

theorem rhoC_of_mem_L {l : G} (hl : l ∈ L) (hlC : l ∈ centralizer ({z} : Set G)) :
    rhoC c ⟨l, hlC⟩ = ((θ ⟨l, hl⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) :=
  rhoC_coe c ⟨l, hl⟩ hlC

theorem rhoC_symm (a : alternatingGroup (Fin n))
    (h : ((θ.symm a : L) : G) ∈ centralizer ({z} : Set G)) :
    rhoC c ⟨θ.symm a, h⟩ = (a : Perm (Fin n)) := by
  rw [rhoC_coe, MulEquiv.apply_symm_apply]

theorem rhoC_w (h : w θ c.hn8 ∈ centralizer ({z} : Set G)) :
    rhoC c ⟨w θ c.hn8, h⟩ = tr c.hn8 1 :=
  (rhoC_symm c (wBar c.hn8) h).trans (coe_wBar c.hn8)

theorem rhoC_eps (i : Fin 8) (h : N0.eps θ c.hn8 i ∈ centralizer ({z} : Set G)) :
    rhoC c ⟨N0.eps θ c.hn8 i, h⟩ = tr c.hn8 i :=
  rhoC_symm c ⟨tr c.hn8 i, tr_mem_alternatingGroup c.hn8 i⟩ h

theorem rhoC_z (h : z ∈ centralizer ({z} : Set G)) : rhoC c ⟨z, h⟩ = 1 :=
  MonoidHom.mem_ker.1 ((mem_ker_rhoC_iff c _).2 (z_mem_centralizer_L c))

theorem w_mem_L : w θ c.hn8 ∈ L := (θ.symm (wBar c.hn8)).2

theorem w_ne_one : w θ c.hn8 ≠ 1 := by
  rw [N0.w_eq_eps]
  intro h
  exact absurd ((N0.eps_eq_one_iff θ c.hn8 1).1 h) (by decide)

theorem w_mul_self : w θ c.hn8 * w θ c.hn8 = 1 := by
  rw [N0.w_eq_eps, N0.eps_mul_self]

theorem w_comm_z : w θ c.hn8 * z = z * w θ c.hn8 :=
  mem_centralizer_singleton_iff.1 (L_le_cent c (w_mem_L c))

end Basic

structure IsHStar (c : Config G L Q n θ z) (H : Subgroup G) (Nbar : Subgroup (Perm (Fin n))) :
    Prop where
  le : H ≤ centralizer ({z} : Set G)
  L_le : L ≤ H
  inj : ∀ h ∈ H, h ∈ centralizer (L : Set G) → h = 1
  surj : ∀ σ ∈ Nbar, ∃ h : centralizer ({z} : Set G), (h : G) ∈ H ∧ rhoC c h = σ

section HStar

variable {c : Config G L Q n θ z} {H : Subgroup G} {Nbar : Subgroup (Perm (Fin n))}

theorem IsHStar.eq_of_rhoC_eq (hH : IsHStar c H Nbar) {a b : centralizer ({z} : Set G)}
    (ha : (a : G) ∈ H) (hb : (b : G) ∈ H) (h : rhoC c a = rhoC c b) : a = b := by
  have hk : a * b⁻¹ ∈ (rhoC c).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have h1 : (a : G) * (b : G)⁻¹ = 1 :=
    hH.inj _ (mul_mem ha (inv_mem hb)) ((mem_ker_rhoC_iff c _).1 hk)
  exact Subtype.ext (mul_inv_eq_one.1 h1)

theorem IsHStar.z_not_mem (hH : IsHStar c H Nbar) : z ∉ H := fun h =>
  z_ne_one c (hH.inj z h (z_mem_centralizer_L c))

theorem IsHStar.w_mem (hH : IsHStar c H Nbar) : w θ c.hn8 ∈ H := hH.L_le (w_mem_L c)

end HStar

theorem isHStar_inner (c : Config G L Q n θ z) : IsHStar c L (alternatingGroup (Fin n)) where
  le := L_le_cent c
  L_le := le_rfl
  inj h hL hK := AltStdBal.eq_one_of_mem_of_mem_centralizer θ (by have := c.hn8; omega) hL hK
  surj σ hσ := ⟨⟨θ.symm ⟨σ, hσ⟩, L_le_cent c (θ.symm ⟨σ, hσ⟩).2⟩, (θ.symm ⟨σ, hσ⟩).2,
    rhoC_symm c ⟨σ, hσ⟩ _⟩

theorem isHStar_outer (c : Config G L Q n θ z) {u : G} (huC : u ∈ centralizer ({z} : Set G))
    (huO : u ∉ L ⊔ centralizer (L : Set G)) (hu2 : u ^ 2 = 1) : IsHStar c (L ⊔ zpowers u) ⊤ where
  le := sup_le (L_le_cent c) (zpowers_le.2 huC)
  L_le := le_sup_left
  inj h hh hK := by
    have huN : u ∈ normalizer (L : Set G) := cent_le_normalizer c.ot.std c.ot.cyc huC
    rcases (mem_sup_zpowers_iff_of_mul_self (by rw [← sq, hu2])
      (fun p hp => (mem_normalizer_iff.1 huN p).1 hp)).1 hh with h1 | h1
    · exact AltStdBal.eq_one_of_mem_of_mem_centralizer θ (by have := c.hn8; omega) h1 hK
    · exfalso
      apply huO
      have : u = h⁻¹ * (h * u) := by group
      rw [this]
      exact mul_mem (mem_sup_right (inv_mem hK)) (mem_sup_left h1)
  surj σ _ := by
    by_cases hσ : σ ∈ alternatingGroup (Fin n)
    · exact ⟨⟨θ.symm ⟨σ, hσ⟩, L_le_cent c (θ.symm ⟨σ, hσ⟩).2⟩,
        mem_sup_left (θ.symm ⟨σ, hσ⟩).2, rhoC_symm c ⟨σ, hσ⟩ _⟩
    · have hu : rhoC c ⟨u, huC⟩ ∉ alternatingGroup (Fin n) := fun h =>
        huO (mem_sup_of_rho_mem θ c.hn8 (cent_le_normalizer c.ot.std c.ot.cyc huC) h)
      have hm : σ * (rhoC c ⟨u, huC⟩)⁻¹ ∈ alternatingGroup (Fin n) := by
        rw [Perm.mem_alternatingGroup] at hσ hu ⊢
        rw [map_mul, map_inv]
        rcases Int.units_eq_one_or (Perm.sign σ) with h | h
        · exact absurd h hσ
        rcases Int.units_eq_one_or (Perm.sign (rhoC c ⟨u, huC⟩)) with h' | h'
        · exact absurd h' hu
        rw [h, h']
        decide
      refine ⟨⟨θ.symm ⟨_, hm⟩, L_le_cent c (θ.symm ⟨_, hm⟩).2⟩ * ⟨u, huC⟩,
        mul_mem (mem_sup_left (θ.symm ⟨_, hm⟩).2) (mem_sup_right (mem_zpowers u)), ?_⟩
      rw [map_mul, rhoC_symm c ⟨_, hm⟩, inv_mul_cancel_right]

section Sylow

variable {c : Config G L Q n θ z} {H : Subgroup G} {Nbar Rbar : Subgroup (Perm (Fin n))}

@[expose] noncomputable def rStar (c : Config G L Q n θ z) (H : Subgroup G)
    (Rbar : Subgroup (Perm (Fin n))) : Subgroup G :=
  H ⊓ (Rbar.comap (rhoC c)).map (centralizer ({z} : Set G)).subtype

theorem mem_rStar_iff' {s : centralizer ({z} : Set G)} :
    (s : G) ∈ rStar c H Rbar ↔ (s : G) ∈ H ∧ rhoC c s ∈ Rbar := by
  unfold rStar
  rw [mem_inf, mem_map]
  refine and_congr Iff.rfl ⟨?_, fun h => ⟨s, h, rfl⟩⟩
  rintro ⟨t, ht, hts⟩
  obtain rfl : t = s := Subtype.ext hts
  exact ht

theorem rStar_le_H : rStar c H Rbar ≤ H := inf_le_left

theorem rStar_le_cent : rStar c H Rbar ≤ centralizer ({z} : Set G) :=
  inf_le_right.trans (map_subtype_le _)

theorem mem_rStar_iff {g : G} : g ∈ rStar c H Rbar ↔
    g ∈ H ∧ ∃ hg : g ∈ centralizer ({z} : Set G), rhoC c ⟨g, hg⟩ ∈ Rbar := by
  constructor
  · intro h
    exact ⟨rStar_le_H h, rStar_le_cent h,
      (mem_rStar_iff' (s := ⟨g, rStar_le_cent h⟩)).1 h |>.2⟩
  · rintro ⟨hH, hg, hR⟩
    exact (mem_rStar_iff' (s := ⟨g, hg⟩)).2 ⟨hH, hR⟩

theorem rhoC_mem_of_mem_rStar {s : centralizer ({z} : Set G)} (hs : (s : G) ∈ rStar c H Rbar) :
    rhoC c s ∈ Rbar :=
  (mem_rStar_iff'.1 hs).2

theorem IsHStar.mem_rStar_of_mem_L (hH : IsHStar c H Nbar) {l : G} (hl : l ∈ L)
    (h : ((θ ⟨l, hl⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) ∈ Rbar) :
    l ∈ rStar c H Rbar :=
  mem_rStar_iff.2 ⟨hH.L_le hl, L_le_cent c hl, by rw [rhoC_of_mem_L c hl]; exact h⟩

theorem IsHStar.E_le_rStar (hH : IsHStar c H Nbar) (htr : ∀ v : Fin 8, tr c.hn8 v ∈ Rbar) :
    E θ c.hn8 ≤ rStar c H Rbar := by
  intro g hg
  obtain ⟨i, rfl⟩ := (N0.mem_E_iff θ c.hn8 g).1 hg
  have hC : N0.eps θ c.hn8 i ∈ centralizer ({z} : Set G) := L_le_cent c (N0.eps_mem_L θ c.hn8 i)
  exact mem_rStar_iff.2 ⟨hH.L_le (N0.eps_mem_L θ c.hn8 i), hC, by rw [rhoC_eps]; exact htr i⟩

theorem IsHStar.w_mem_rStar (hH : IsHStar c H Nbar) (htr : ∀ v : Fin 8, tr c.hn8 v ∈ Rbar) :
    w θ c.hn8 ∈ rStar c H Rbar := by
  rw [N0.w_eq_eps]
  exact hH.E_le_rStar htr (N0.eps_mem_E θ c.hn8 1)

theorem IsHStar.card_rStar (hH : IsHStar c H Nbar) (hle : Rbar ≤ Nbar) :
    Nat.card (rStar c H Rbar) = Nat.card Rbar := by
  have hC : ∀ r : rStar c H Rbar, (r : G) ∈ centralizer ({z} : Set G) := fun r =>
    rStar_le_cent r.2
  have hR : ∀ r : rStar c H Rbar, rhoC c ⟨r, hC r⟩ ∈ Rbar := fun r =>
    (mem_rStar_iff' (c := c) (H := H) (Rbar := Rbar) (s := ⟨r, hC r⟩)).1 r.2 |>.2
  let f : rStar c H Rbar → Rbar := fun r => ⟨rhoC c ⟨r, hC r⟩, hR r⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h1 : rhoC c ⟨a, hC a⟩ = rhoC c ⟨b, hC b⟩ := congrArg Subtype.val hab
      have h2 := hH.eq_of_rhoC_eq (rStar_le_H a.2) (rStar_le_H b.2) h1
      have h3 : (a : G) = b := congrArg (fun t : centralizer ({z} : Set G) => (t : G)) h2
      exact Subtype.ext h3
    · rintro ⟨σ, hσ⟩
      obtain ⟨h, hhH, hρ⟩ := hH.surj σ (hle hσ)
      have hhR : (h : G) ∈ rStar c H Rbar := mem_rStar_iff'.2 ⟨hhH, hρ ▸ hσ⟩
      exact ⟨⟨h, hhR⟩, Subtype.ext hρ⟩
  exact Nat.card_eq_of_bijective f hf

@[expose] noncomputable def sSyl (c : Config G L Q n θ z) (H : Subgroup G)
    (Rbar : Subgroup (Perm (Fin n))) : Subgroup G :=
  rStar c H Rbar ⊔ zpowers z

theorem rStar_le_sSyl : rStar c H Rbar ≤ sSyl c H Rbar := le_sup_left

theorem z_mem_sSyl : z ∈ sSyl c H Rbar := mem_sup_right (mem_zpowers z)

theorem conj_z_mem_rStar {r : G} (hr : r ∈ rStar c H Rbar) : z * r * z⁻¹ ∈ rStar c H Rbar := by
  have hrz : r * z = z * r := mem_centralizer_singleton_iff.1 (rStar_le_cent hr)
  rw [← hrz, mul_inv_cancel_right]
  exact hr

theorem mem_sSyl_iff {g : G} :
    g ∈ sSyl c H Rbar ↔ g ∈ rStar c H Rbar ∨ g * z ∈ rStar c H Rbar :=
  mem_sup_zpowers_iff_of_mul_self (z_mul_self c) (fun _ hr => conj_z_mem_rStar hr)

theorem sSyl_le_cent : sSyl c H Rbar ≤ centralizer ({z} : Set G) :=
  sup_le rStar_le_cent (zpowers_le.2 (self_mem_centralizer_singleton z))

theorem IsHStar.z_not_mem_rStar (hH : IsHStar c H Nbar) : z ∉ rStar c H Rbar := fun h =>
  hH.z_not_mem (rStar_le_H h)

theorem IsHStar.card_sSyl (hH : IsHStar c H Nbar) :
    Nat.card (sSyl c H Rbar) = 2 * Nat.card (rStar c H Rbar) :=
  card_sup_zpowers_of_mul_self (z_mul_self c) (fun _ hr => conj_z_mem_rStar hr) hH.z_not_mem_rStar

theorem IsHStar.relIndex_rStar (hH : IsHStar c H Nbar) :
    (rStar c H Rbar).relIndex (sSyl c H Rbar) = 2 := by
  have h := relIndex_mul_card (rStar c H Rbar) (sSyl c H Rbar)
  rw [inf_of_le_left rStar_le_sSyl, hH.card_sSyl] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h

theorem rhoC_mem_of_mem_sSyl {s : centralizer ({z} : Set G)} (hs : (s : G) ∈ sSyl c H Rbar) :
    rhoC c s ∈ Rbar := by
  rcases mem_sSyl_iff.1 hs with h | h
  · exact rhoC_mem_of_mem_rStar h
  · have h1 := rhoC_mem_of_mem_rStar (s := s * ⟨z, self_mem_centralizer_singleton z⟩) h
    rwa [map_mul, rhoC_z, mul_one] at h1

theorem IsHStar.comm_of_rhoC_comm (hH : IsHStar c H Nbar) {a b : centralizer ({z} : Set G)}
    (ha : (a : G) ∈ sSyl c H Rbar) (hb : (b : G) ∈ sSyl c H Rbar)
    (h : rhoC c a * rhoC c b = rhoC c b * rhoC c a) : (a : G) * b = b * a := by
  have hD : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ rStar c H Rbar := by
    have := AltStdSmall.commutator_le_of_relIndex_two hH.relIndex_rStar
      (commutator_mem_commutator ha hb)
    rwa [commutatorElement_def] at this
  have h1 : a * b * a⁻¹ * b⁻¹ = 1 := hH.eq_of_rhoC_eq (rStar_le_H hD) (one_mem H) (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_one, h]
    group)
  have h2 : a * b = b * a := by
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  exact congrArg Subtype.val h2

variable {k : ℕ} {cc : Subgroup (Perm (Fin n)) → Prop}

theorem IsHStar.card_sSyl_eq (hH : IsHStar c H Nbar) (hR : FusR n c.hn8 Nbar Rbar k cc) :
    Nat.card (sSyl c H Rbar) = 2 ^ (k + 1) := by
  rw [hH.card_sSyl, hH.card_rStar hR.le, hR.card, pow_succ, mul_comm]

theorem IsHStar.sSyl_maximal (hH : IsHStar c H Nbar) (hR : FusR n c.hn8 Nbar Rbar k cc)
    (hk : ∀ P : Sylow 2 (centralizer ({z} : Set G)), Nat.card P = 2 ^ (k + 1))
    (P : Subgroup G) (hP : IsPGroup 2 P) (hSP : sSyl c H Rbar ≤ P)
    (hPC : P ≤ centralizer ({z} : Set G)) : P = sSyl c H Rbar := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf (centralizer ({z} : Set G))) :=
    hP.of_equiv (subgroupOfEquivOfLe hPC).symm
  obtain ⟨P', hP'le⟩ := hP'.exists_le_sylow
  have h1 : Nat.card P ≤ Nat.card P' := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hPC).toEquiv]
    exact Subgroup.card_le_of_le hP'le
  rw [hk] at h1
  exact (Subgroup.eq_of_le_of_card_ge hSP (by rw [hH.card_sSyl_eq hR]; exact h1)).symm

theorem IsHStar.eq_of_mem_rStar_central (hH : IsHStar c H Nbar) (hR : FusR n c.hn8 Nbar Rbar k cc)
    {r : G} (hr : r ∈ rStar c H Rbar) (hc : ∀ s ∈ sSyl c H Rbar, r * s = s * r) :
    r = 1 ∨ r = w θ c.hn8 := by
  obtain ⟨hrH, hrC, hrR⟩ := mem_rStar_iff.1 hr
  have key : ∀ s ∈ Rbar, rhoC c ⟨r, hrC⟩ * s = s * rhoC c ⟨r, hrC⟩ := by
    intro s hs
    obtain ⟨h, hhH, hρ⟩ := hH.surj s (hR.le hs)
    have hhR : (h : G) ∈ rStar c H Rbar := mem_rStar_iff'.2 ⟨hhH, hρ ▸ hs⟩
    have h2 : (⟨r, hrC⟩ : centralizer ({z} : Set G)) * h = h * ⟨r, hrC⟩ :=
      Subtype.ext (hc _ (rStar_le_sSyl hhR))
    rw [← hρ, ← map_mul, ← map_mul, h2]
  have hwC : w θ c.hn8 ∈ centralizer ({z} : Set G) := L_le_cent c (w_mem_L c)
  rcases hR.center _ hrR key with h1 | h1
  · left
    have : (⟨r, hrC⟩ : centralizer ({z} : Set G)) = 1 :=
      hH.eq_of_rhoC_eq hrH (one_mem H) (by rw [h1, map_one])
    exact congrArg Subtype.val this
  · right
    have : (⟨r, hrC⟩ : centralizer ({z} : Set G)) = ⟨w θ c.hn8, hwC⟩ :=
      hH.eq_of_rhoC_eq hrH hH.w_mem (by rw [h1, rhoC_w])
    exact congrArg Subtype.val this

theorem IsHStar.w_mem_commutator (hH : IsHStar c H Nbar) (hR : FusR n c.hn8 Nbar Rbar k cc) :
    w θ c.hn8 ∈ ⁅sSyl c H Rbar, sSyl c H Rbar⁆ := by
  obtain ⟨a, ha, b, hb, hab⟩ := hR.comm
  obtain ⟨a', ha'H, ha'ρ⟩ := hH.surj a (hR.le ha)
  obtain ⟨b', hb'H, hb'ρ⟩ := hH.surj b (hR.le hb)
  have ha'R : (a' : G) ∈ rStar c H Rbar := mem_rStar_iff'.2 ⟨ha'H, ha'ρ ▸ ha⟩
  have hb'R : (b' : G) ∈ rStar c H Rbar := mem_rStar_iff'.2 ⟨hb'H, hb'ρ ▸ hb⟩
  have hwC : w θ c.hn8 ∈ centralizer ({z} : Set G) := L_le_cent c (w_mem_L c)
  have hmem : ((a' * b' * a'⁻¹ * b'⁻¹ : centralizer ({z} : Set G)) : G) ∈ H :=
    mul_mem (mul_mem (mul_mem ha'H hb'H) (inv_mem ha'H)) (inv_mem hb'H)
  have h1 : a' * b' * a'⁻¹ * b'⁻¹ = ⟨w θ c.hn8, hwC⟩ := hH.eq_of_rhoC_eq hmem hH.w_mem (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ha'ρ, hb'ρ, hab, rhoC_w])
  have h2 : ⁅(a' : G), (b' : G)⁆ = w θ c.hn8 := by
    rw [commutatorElement_def]
    exact congrArg Subtype.val h1
  rw [← h2]
  exact commutator_mem_commutator (rStar_le_sSyl ha'R) (rStar_le_sSyl hb'R)

end Sylow

end CFSG.OddStandard.AltStdSmall4.Fus.Main
