module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameSylow
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

theorem mem_zpowers_of_sq {G : Type} [Group G] {x : G} (h : x * x = 1) {b : G} :
    b ∈ zpowers x ↔ b = 1 ∨ b = x := by
  have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact h
  constructor
  · intro hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · left
      rw [hm, zpow_mul, h2, one_zpow]
    · right
      rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  · intro hb
    rcases hb with hb | hb
    · rw [hb]
      exact one_mem _
    · rw [hb]
      exact Subgroup.mem_zpowers _

namespace PspFrame

variable {G : Type} [Group G] {L : Subgroup G}

structure Setup1051 (F : PspFrame L) (t : G) (Q U : Subgroup G) (Qm : Subgroup P45) : Prop where
  Q_le_L : Q ≤ L
  img_Q : F.img Q = Qm
  t_sq : t * t = 1
  t_ne : t ≠ 1
  t_cent : t ∈ centralizer (L : Set G)
  U_le_N : U ≤ normalizer (L : Set G)
  W_le_U : Q ⊔ zpowers t ≤ U
  cent_U : centralizer (L : Set G) ⊓ U = zpowers t

theorem phi_mem_zpowers (F : PspFrame L) (zL : ↥L) {y : G} (hy : y ∈ zpowers (zL : G))
    (hN : y ∈ normalizer (L : Set G)) : F.φ ⟨y, hN⟩ ∈ zpowers (F.ψ zL) := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have h1 : (⟨(zL : G) ^ k, hN⟩ : ↥(normalizer (L : Set G))) =
      ⟨(zL : G), Subgroup.le_normalizer zL.2⟩ ^ k := rfl
  rw [h1, map_zpow]
  exact Subgroup.zpow_mem_zpowers _ _

theorem phi_commutator (F : PspFrame L) {u v : G} (hu : u ∈ normalizer (L : Set G))
    (hv : v ∈ normalizer (L : Set G)) (h : u * v * u⁻¹ * v⁻¹ ∈ normalizer (L : Set G)) :
    F.φ ⟨u * v * u⁻¹ * v⁻¹, h⟩ =
      F.φ ⟨u, hu⟩ * F.φ ⟨v, hv⟩ * (F.φ ⟨u, hu⟩)⁻¹ * (F.φ ⟨v, hv⟩)⁻¹ := by
  have h2 : (⟨u * v * u⁻¹ * v⁻¹, h⟩ : ↥(normalizer (L : Set G))) =
      ⟨u, hu⟩ * ⟨v, hv⟩ * ⟨u, hu⟩⁻¹ * ⟨v, hv⟩⁻¹ := rfl
  rw [h2, map_mul, map_mul, map_mul, map_inv, map_inv]

theorem phi_mul_self (F : PspFrame L) {u : G} (hu : u ∈ normalizer (L : Set G))
    (h : u * u ∈ normalizer (L : Set G)) : F.φ ⟨u * u, h⟩ = F.φ ⟨u, hu⟩ * F.φ ⟨u, hu⟩ := by
  have h2 : (⟨u * u, h⟩ : ↥(normalizer (L : Set G))) = ⟨u, hu⟩ * ⟨u, hu⟩ := rfl
  rw [h2, map_mul]

variable {F : PspFrame L} {t : G} {Q U : Subgroup G} {Qm : Subgroup P45}
  (S : Setup1051 F t Q U Qm)

namespace Setup1051

include S

theorem t_mem_N : t ∈ normalizer (L : Set G) :=
  Subgroup.centralizer_le_normalizer (L : Set G) S.t_cent

theorem t_not_mem_L : t ∉ L := by
  intro htL
  have h1 : F.φ ⟨t, S.t_mem_N⟩ = 1 := (F.ker_iff _).2 S.t_cent
  have h2 : (⟨t, S.t_mem_N⟩ : ↥(normalizer (L : Set G))) = 1 :=
    F.inj_L _ 1 htL L.one_mem (by rw [h1, map_one])
  exact S.t_ne (congrArg Subtype.val h2)

theorem t_not_mem_Q : t ∉ Q := fun h => S.t_not_mem_L (S.Q_le_L h)

theorem comm_Q_t {q : G} (hq : q ∈ Q) : q * t = t * q :=
  Subgroup.mem_centralizer_iff.1 S.t_cent q (S.Q_le_L hq)

theorem mem_W_cases {w : G} (hw : w ∈ Q ⊔ zpowers t) : w ∈ Q ∨ w * t ∈ Q := by
  have hcomm : ∀ a ∈ Q, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    rcases (mem_zpowers_of_sq S.t_sq).1 hb with h | h
    · rw [h, mul_one, one_mul]
    · rw [h]
      exact S.comm_Q_t ha
  obtain ⟨a, ha, b, hb, hab⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hw
  rw [← hab]
  rcases (mem_zpowers_of_sq S.t_sq).1 hb with h | h
  · left
    rw [h, mul_one]
    exact ha
  · right
    rw [h, mul_assoc, S.t_sq, mul_one]
    exact ha

theorem phi_mul_t {w : G} (hN : w ∈ normalizer (L : Set G))
    (hwt : w * t ∈ normalizer (L : Set G)) : F.φ ⟨w * t, hwt⟩ = F.φ ⟨w, hN⟩ := by
  have : (⟨w * t, hwt⟩ : ↥(normalizer (L : Set G))) = ⟨w, hN⟩ * ⟨t, S.t_mem_N⟩ := rfl
  rw [this, map_mul, (F.ker_iff ⟨t, S.t_mem_N⟩).2 S.t_cent, mul_one]

theorem phi_mem {w : G} (hw : w ∈ Q ⊔ zpowers t) (hN : w ∈ normalizer (L : Set G)) :
    F.φ ⟨w, hN⟩ ∈ Qm := by
  rw [← S.img_Q]
  rcases S.mem_W_cases hw with h | h
  · have hL : w ∈ L := S.Q_le_L h
    have h1 : F.φ ⟨w, hN⟩ = F.ψ ⟨w, hL⟩ := rfl
    rw [h1]
    exact psi_mem_img.2 h
  · have hL : w * t ∈ L := S.Q_le_L h
    have hwtN : w * t ∈ normalizer (L : Set G) := (normalizer (L : Set G)).mul_mem hN S.t_mem_N
    rw [← S.phi_mul_t hN hwtN]
    have h1 : F.φ ⟨w * t, hwtN⟩ = F.ψ ⟨w * t, hL⟩ := rfl
    rw [h1]
    exact psi_mem_img.2 h

theorem exists_of_mem_Qm {q : P45} (hq : q ∈ Qm) : ∃ l : ↥L, (l : G) ∈ Q ∧ F.ψ l = q := by
  rw [← S.img_Q] at hq
  exact mem_img.1 hq

theorem mem_W_iff {u : G} (hu : u ∈ U) :
    u ∈ Q ⊔ zpowers t ↔ F.φ ⟨u, S.U_le_N hu⟩ ∈ Qm := by
  refine ⟨fun h => S.phi_mem h _, fun h => ?_⟩
  obtain ⟨l, hlQ, hl⟩ := S.exists_of_mem_Qm h
  have hlN : (l : G) ∈ normalizer (L : Set G) := Subgroup.le_normalizer l.2
  have hlU : (l : G) ∈ U := S.W_le_U (Subgroup.mem_sup_left hlQ)
  have hψ : F.φ ⟨(l : G), hlN⟩ = F.ψ l := rfl
  have hker : F.φ (⟨(l : G), hlN⟩⁻¹ * ⟨u, S.U_le_N hu⟩) = 1 := by
    rw [map_mul, map_inv, hψ, hl, inv_mul_cancel]
  have hc : (l : G)⁻¹ * u ∈ centralizer (L : Set G) := (F.ker_iff _).1 hker
  have hcU : (l : G)⁻¹ * u ∈ U := U.mul_mem (U.inv_mem hlU) hu
  have hT : (l : G)⁻¹ * u ∈ zpowers t := S.cent_U ▸ Subgroup.mem_inf.2 ⟨hc, hcU⟩
  have h2 : u = (l : G) * ((l : G)⁻¹ * u) := by group
  rw [h2]
  exact Subgroup.mul_mem_sup hlQ hT

@[expose] def phiU : ↥U →* P45 := F.φ.comp (Subgroup.inclusion S.U_le_N)

theorem relIndex_phiU : Qm.relIndex S.phiU.range = (Q ⊔ zpowers t).relIndex U := by
  have h : (Q ⊔ zpowers t).subgroupOf U = Qm.comap S.phiU := by
    ext u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    exact S.mem_W_iff u.2
  rw [← Subgroup.index_comap, ← h]
  rfl

theorem mem_dbar (zL : ↥L) {z0' : P45} (hψz : F.ψ zL = z0') {w : G} (hw : w ∈ Q ⊔ zpowers t)
    (hD : ∀ u ∈ U, w * u * w⁻¹ * u⁻¹ ∈ zpowers (zL : G)) :
    F.φ ⟨w, S.U_le_N (S.W_le_U hw)⟩ ∈ Qm ∧ ∀ x ∈ S.phiU.range,
      F.φ ⟨w, S.U_le_N (S.W_le_U hw)⟩ * x * (F.φ ⟨w, S.U_le_N (S.W_le_U hw)⟩)⁻¹ * x⁻¹ ∈
        zpowers z0' := by
  refine ⟨S.phi_mem hw _, ?_⟩
  rintro _ ⟨⟨u, hu⟩, rfl⟩
  have hwN := S.U_le_N (S.W_le_U hw)
  have huN := S.U_le_N hu
  have hcN : w * u * w⁻¹ * u⁻¹ ∈ normalizer (L : Set G) :=
    (normalizer (L : Set G)).mul_mem ((normalizer (L : Set G)).mul_mem
      ((normalizer (L : Set G)).mul_mem hwN huN) ((normalizer (L : Set G)).inv_mem hwN))
      ((normalizer (L : Set G)).inv_mem huN)
  have h1 : F.φ ⟨w * u * w⁻¹ * u⁻¹, hcN⟩ =
      F.φ ⟨w, hwN⟩ * S.phiU ⟨u, hu⟩ * (F.φ ⟨w, hwN⟩)⁻¹ * (S.phiU ⟨u, hu⟩)⁻¹ :=
    phi_commutator F hwN huN hcN
  rw [← h1, ← hψz]
  exact phi_mem_zpowers F zL (hD u hu) hcN

theorem inj {w w' : G} (hw : w ∈ Q ⊔ zpowers t) (hw' : w' ∈ Q ⊔ zpowers t)
    (hφ : F.φ ⟨w, S.U_le_N (S.W_le_U hw)⟩ = F.φ ⟨w', S.U_le_N (S.W_le_U hw')⟩)
    (hQ : w ∈ Q ↔ w' ∈ Q) : w = w' := by
  have hwU := S.W_le_U hw
  have hwU' := S.W_le_U hw'
  have hker : F.φ (⟨w, S.U_le_N hwU⟩⁻¹ * ⟨w', S.U_le_N hwU'⟩) = 1 := by
    rw [map_mul, map_inv, hφ, inv_mul_cancel]
  have hc : w⁻¹ * w' ∈ centralizer (L : Set G) := (F.ker_iff _).1 hker
  have hcU : w⁻¹ * w' ∈ U := U.mul_mem (U.inv_mem hwU) hwU'
  have hT : w⁻¹ * w' ∈ zpowers t := S.cent_U ▸ Subgroup.mem_inf.2 ⟨hc, hcU⟩
  rcases (mem_zpowers_of_sq S.t_sq).1 hT with h | h
  · exact inv_mul_eq_one.1 h
  · have hw'eq : w' = w * t := by rw [← h]; group
    have ht : t = w⁻¹ * w' := by rw [hw'eq]; group
    exfalso
    rcases S.mem_W_cases hw with hq | hq
    · have h1 : w' ∉ Q := fun h' => S.t_not_mem_Q (ht ▸ Q.mul_mem (Q.inv_mem hq) h')
      exact h1 (hQ.1 hq)
    · have hq' : w' ∈ Q := hw'eq ▸ hq
      have h1 : w ∉ Q := fun h' => S.t_not_mem_Q (ht ▸ Q.mul_mem (Q.inv_mem h') hq')
      exact h1 (hQ.2 hq')

theorem two_mul_card_le [Finite G] : 2 * Nat.card Qm ≤ Nat.card ↥(Q ⊔ zpowers t) := by
  classical
  let f : ↥(Q ⊔ zpowers t) → ↥Qm × Bool := fun w =>
    (⟨F.φ ⟨w.1, S.U_le_N (S.W_le_U w.2)⟩, S.phi_mem w.2 _⟩, decide (w.1 ∈ Q))
  have hf : Function.Surjective f := by
    rintro ⟨⟨q, hq⟩, b⟩
    obtain ⟨l, hlQ, hl⟩ := S.exists_of_mem_Qm hq
    have hlN : (l : G) ∈ normalizer (L : Set G) := Subgroup.le_normalizer l.2
    have hψ : F.φ ⟨(l : G), hlN⟩ = F.ψ l := rfl
    cases b
    · have hwt : (l : G) * t ∈ Q ⊔ zpowers t :=
        Subgroup.mul_mem_sup hlQ (Subgroup.mem_zpowers t)
      refine ⟨⟨(l : G) * t, hwt⟩, Prod.ext (Subtype.ext ?_) ?_⟩
      · show F.φ ⟨(l : G) * t, _⟩ = q
        rw [S.phi_mul_t hlN, hψ, hl]
      · show decide ((l : G) * t ∈ Q) = false
        rw [decide_eq_false_iff_not]
        intro h
        apply S.t_not_mem_Q
        have h1 := Q.mul_mem (Q.inv_mem hlQ) h
        simpa using h1
    · refine ⟨⟨(l : G), Subgroup.mem_sup_left hlQ⟩, Prod.ext (Subtype.ext ?_) ?_⟩
      · show F.φ ⟨(l : G), _⟩ = q
        rw [hψ, hl]
      · show decide ((l : G) ∈ Q) = true
        exact decide_eq_true hlQ
  have h1 := Nat.card_le_card_of_surjective f hf
  have hb : Nat.card Bool = 2 := by simp
  rw [Nat.card_prod, hb] at h1
  omega

theorem card_dset_le [Finite G] (zL : ↥L) {z0' : P45} (hψz : F.ψ zL = z0') :
    Nat.card {w : G // w ∈ Q ⊔ zpowers t ∧ ∀ u ∈ U, w * u * w⁻¹ * u⁻¹ ∈ zpowers (zL : G)} ≤
      Nat.card {q : P45 // q ∈ Qm ∧ ∀ x ∈ S.phiU.range, q * x * q⁻¹ * x⁻¹ ∈ zpowers z0'} * 2 := by
  classical
  let f : {w : G // w ∈ Q ⊔ zpowers t ∧ ∀ u ∈ U, w * u * w⁻¹ * u⁻¹ ∈ zpowers (zL : G)} →
      {q : P45 // q ∈ Qm ∧ ∀ x ∈ S.phiU.range, q * x * q⁻¹ * x⁻¹ ∈ zpowers z0'} × Bool :=
    fun w => (⟨F.φ ⟨w.1, S.U_le_N (S.W_le_U w.2.1)⟩, S.mem_dbar zL hψz w.2.1 w.2.2⟩,
      decide (w.1 ∈ Q))
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : F.φ ⟨a.1, S.U_le_N (S.W_le_U a.2.1)⟩ = F.φ ⟨b.1, S.U_le_N (S.W_le_U b.2.1)⟩ :=
      congrArg (fun p => p.1.1) hab
    have h2 : decide (a.1 ∈ Q) = decide (b.1 ∈ Q) := congrArg Prod.snd hab
    exact Subtype.ext (S.inj a.2.1 b.2.1 h1 (decide_eq_decide.1 h2))
  have h3 := Nat.card_le_card_of_injective f hf
  have hb : Nat.card Bool = 2 := by simp
  rwa [Nat.card_prod, hb] at h3

end Setup1051

end PspFrame

end CFSG.OddStandard.SmallF3.Omega
