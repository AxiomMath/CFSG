module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.AutCount

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G : Type} [Group G]

structure NData (L : Subgroup G) (F : Subgroup G) : Prop where
  F_le : F ≤ L
  F_comm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x
  F_sq : ∀ x ∈ F, x * x = 1
  F_card : Nat.card F = 16
  F_self : ∀ x ∈ L, (∀ f ∈ F, x * f = f * x) → x ∈ F
  N_two : 128 ∣ Nat.card ↥(normalizer (F : Set G) ⊓ L)
  trans : ∀ f ∈ F, f ≠ 1 → ∀ f' ∈ F, f' ≠ 1 →
    ∃ b ∈ L, (∀ x, x ∈ F ↔ b * x * b⁻¹ ∈ F) ∧ b * f * b⁻¹ = f'

variable {L : Subgroup G} {z t : G} {F : Subgroup G}

section Basic

theorem isConj_z_mul (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) {f : G} (hf : f ∈ F) :
    IsConj z (z * f) := by
  by_cases hf1 : f = 1
  · subst hf1
    rw [mul_one]
  · rw [h.z_comm f (D.F_le hf)]
    exact hZ f (D.F_le hf) (D.F_sq f hf) hf1

theorem mem_mul_of_isConj (h : OneClassData L z t) (D : NData L F) {e : G}
    (he : e ∈ F ⊔ zpowers z) (hconj : IsConj z e) : ∃ f ∈ F, e = z * f := by
  obtain ⟨f, hf, b, hb, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (zpowers_le_centralizer_of_le h D.F_le) he
  rcases mem_zpowers_involution h.z_mul_self hb with rfl | rfl
  · exfalso
    rw [mul_one] at hconj
    by_cases hf1 : f = 1
    · subst hf1
      exact h.z_ne_one (isConj_one_right.1 hconj.symm)
    · exact h.not_isConj_z_of_mem (D.F_le hf) (D.F_sq f hf) hf1 hconj
  · exact ⟨f, hf, (h.z_comm f (D.F_le hf)).symm⟩

theorem normalizes_F [Finite G] (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) {c : G}
    (hc : ∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) :
    ∀ x, x ∈ F ↔ c * x * c⁻¹ ∈ F := by
  apply forall_mem_iff_of_forall_mem
  intro x hx
  have hxE : c * x * c⁻¹ ∈ F ⊔ zpowers z := (hc x).1 (Subgroup.mem_sup_left hx)
  obtain ⟨f, hf, b, hb, hfb⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (zpowers_le_centralizer_of_le h D.F_le) hxE
  rcases mem_zpowers_involution h.z_mul_self hb with hb1 | hbz
  · rw [hfb, hb1, mul_one]
    exact hf
  · exfalso
    rw [hbz] at hfb
    have h1 : IsConj z (c * x * c⁻¹) := by
      rw [hfb, ← h.z_comm f (D.F_le hf)]
      exact isConj_z_mul h hZ D hf
    have h2 : IsConj x (c * x * c⁻¹) := isConj_iff.2 ⟨c, rfl⟩
    have h3 : IsConj z x := h1.trans h2.symm
    by_cases hx1 : x = 1
    · subst hx1
      exact h.z_ne_one (isConj_one_right.1 h3.symm)
    · exact h.not_isConj_z_of_mem (D.F_le hx) (D.F_sq x hx) hx1 h3

end Basic

section Main

@[expose] def Ksub (z : G) (F : Subgroup G) : Subgroup G :=
  normalizer ((F ⊔ zpowers z : Subgroup G) : Set G) ⊓ centralizer (F : Set G)

theorem mem_Ksub {z : G} {F : Subgroup G} {k : G} :
    k ∈ Ksub z F ↔ (∀ x, x ∈ F ⊔ zpowers z ↔ k * x * k⁻¹ ∈ F ⊔ zpowers z) ∧
      ∀ f ∈ F, f * k = k * f := by
  unfold Ksub
  rw [Subgroup.mem_inf, Subgroup.mem_normalizer_iff, mem_centralizer_iff]
  exact Iff.rfl

theorem E_comm_F (h : OneClassData L z t) (D : NData L F) {e : G} (he : e ∈ F ⊔ zpowers z)
    {f : G} (hf : f ∈ F) : e * f = f * e := by
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (zpowers_le_centralizer_of_le h D.F_le) he
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have h1 : Commute a f := D.F_comm a ha f hf
  have h2 : Commute (z ^ k) f := (show Commute z f from h.z_comm f (D.F_le hf)).zpow_left k
  exact (h1.mul_left h2).eq

theorem E_le_K (h : OneClassData L z t) (D : NData L F) : F ⊔ zpowers z ≤ Ksub z F := by
  intro e he
  rw [mem_Ksub]
  refine ⟨fun x => ?_, fun f hf => (E_comm_F h D he hf).symm⟩
  have := (Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer he) x)
  exact this

theorem conj_z_mem (h : OneClassData L z t) (D : NData L F) {k : G}
    (hk : ∀ x, x ∈ F ⊔ zpowers z ↔ k * x * k⁻¹ ∈ F ⊔ zpowers z) :
    ∃ f ∈ F, k * z * k⁻¹ = z * f := by
  refine mem_mul_of_isConj h D ((hk z).1 (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))) ?_
  exact (isConj_iff.2 ⟨k, rfl⟩ : IsConj z (k * z * k⁻¹))

@[expose] def phiv (z k : G) : G := z * (k * z * k⁻¹)

theorem phiv_mem (h : OneClassData L z t) (D : NData L F) {k : G} (hk : k ∈ Ksub z F) :
    phiv z k ∈ F := by
  obtain ⟨f, hf, hkf⟩ := conj_z_mem h D (mem_Ksub.1 hk).1
  unfold phiv
  rw [hkf, ← mul_assoc, h.z_mul_self, one_mul]
  exact hf

theorem phiv_mul (h : OneClassData L z t) (D : NData L F) {k k' : G} (hk : k ∈ Ksub z F)
    (hk' : k' ∈ Ksub z F) : phiv z (k * k') = phiv z k * phiv z k' := by
  have hpF : phiv z k' ∈ F := phiv_mem h D hk'
  have hcomm : phiv z k' * k = k * phiv z k' := (mem_Ksub.1 hk).2 _ hpF
  have hkp : k * phiv z k' * k⁻¹ = phiv z k' := by
    rw [← hcomm]
    group
  have hu' : k' * z * k'⁻¹ = z * phiv z k' := by
    unfold phiv
    rw [← mul_assoc, h.z_mul_self, one_mul]
  calc phiv z (k * k') = z * (k * (k' * z * k'⁻¹) * k⁻¹) := by unfold phiv; group
    _ = z * (k * (z * phiv z k') * k⁻¹) := by rw [hu']
    _ = z * (k * z * k⁻¹) * (k * phiv z k' * k⁻¹) := by group
    _ = z * (k * z * k⁻¹) * phiv z k' := by rw [hkp]
    _ = phiv z k * phiv z k' := rfl

@[expose] def phiHom (h : OneClassData L z t) (D : NData L F) : Ksub z F →* F :=
  MonoidHom.mk' (fun k => ⟨phiv z k, phiv_mem h D k.2⟩) (fun k k' =>
    Subtype.ext (phiv_mul h D k.2 k'.2))

theorem phiv_eq_one_iff (h : OneClassData L z t) (D : NData L F) {k : G} (hk : k ∈ Ksub z F) :
    phiv z k = 1 ↔ k ∈ F ⊔ zpowers z := by
  constructor
  · intro h1
    have hkz : k * z * k⁻¹ = z := by
      unfold phiv at h1
      rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right h.z_mul_self]
    have hkz' : k * z = z * k := mul_inv_eq_iff_eq_mul.1 hkz
    have hkC : k ∈ L ⊔ zpowers z := by
      rw [← centralizer_z_eq h]
      exact mem_centralizer_singleton_iff.2 hkz'
    obtain ⟨l, hl, b, hb, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_centralizer (zpowers_le_centralizer_of_le h le_rfl) hkC
    have hlF : l ∈ F := by
      refine D.F_self l hl fun f hf => ?_
      have e1 := (mem_Ksub.1 hk).2 f hf
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      have e2 : z ^ j * f = f * z ^ j :=
        (show Commute z f from h.z_comm f (D.F_le hf)).zpow_left j |>.eq
      have e3 : f * l * z ^ j = l * f * z ^ j := by
        calc f * l * z ^ j = f * (l * z ^ j) := by rw [mul_assoc]
          _ = l * z ^ j * f := e1
          _ = l * (z ^ j * f) := by rw [mul_assoc]
          _ = l * (f * z ^ j) := by rw [e2]
          _ = l * f * z ^ j := by rw [mul_assoc]
      exact (mul_right_cancel e3).symm
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hlF) (Subgroup.mem_sup_right hb)
  · intro he
    obtain ⟨f, hf, b, hb, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_centralizer (zpowers_le_centralizer_of_le h D.F_le) he
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hfz : Commute f z := (h.z_comm f (D.F_le hf)).symm
    have hbz : Commute (z ^ j) z := (Commute.refl z).zpow_left j
    have hkz : f * z ^ j * z = z * (f * z ^ j) := (hfz.mul_left hbz).eq
    unfold phiv
    rw [hkz]
    calc z * (z * (f * z ^ j) * (f * z ^ j)⁻¹) = (z * z) * (f * z ^ j * (f * z ^ j)⁻¹) := by
          simp only [mul_assoc]
      _ = 1 := by rw [h.z_mul_self]; group

theorem N_inf_centralizer_eq [Finite G] (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) :
    normalizer ((F ⊔ zpowers z : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) =
      (normalizer (F : Set G) ⊓ L) ⊔ zpowers z := by
  apply le_antisymm
  · intro c hc
    obtain ⟨hcN, hcC⟩ := Subgroup.mem_inf.1 hc
    have hcN' := Subgroup.mem_normalizer_iff.1 hcN
    have hcC' : c * z = z * c := mem_centralizer_singleton_iff.1 hcC
    have hcL : c ∈ L ⊔ zpowers z := by
      rw [← centralizer_z_eq h]
      exact hcC
    obtain ⟨l, hl, b, hb, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_centralizer (zpowers_le_centralizer_of_le h le_rfl) hcL
    have hbE : b ∈ F ⊔ zpowers z := Subgroup.mem_sup_right hb
    have hbN : b ∈ normalizer ((F ⊔ zpowers z : Subgroup G) : Set G) :=
      Subgroup.le_normalizer hbE
    have hlN : l ∈ normalizer ((F ⊔ zpowers z : Subgroup G) : Set G) := by
      have := Subgroup.mul_mem _ hcN (Subgroup.inv_mem _ hbN)
      simpa using this
    have hlF := normalizes_F h hZ D (Subgroup.mem_normalizer_iff.1 hlN)
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_inf.2
      ⟨Subgroup.mem_normalizer_iff.2 hlF, hl⟩)) (Subgroup.mem_sup_right hb)
  · refine sup_le (fun a ha => ?_) ?_
    · obtain ⟨haN, haL⟩ := Subgroup.mem_inf.1 ha
      have haz : a * z * a⁻¹ = z := by
        rw [← h.z_comm a haL]
        group
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_normalizer_iff.2 ?_, ?_⟩
      · exact mem_normalizer_sup h D.F_le (Subgroup.mem_normalizer_iff.1 haN) (Subgroup.one_mem _)
          (by rw [haz, mul_one])
      · exact mem_centralizer_singleton_iff.2 (h.z_comm a haL).symm
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer (Subgroup.mem_sup_right
        (Subgroup.mem_zpowers z)), mem_centralizer_singleton_iff.2 rfl⟩

theorem card_N [Finite G] (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f) :
    Nat.card ↥(normalizer ((F ⊔ zpowers z : Subgroup G) : Set G)) =
      32 * Nat.card ↥(normalizer (F : Set G) ⊓ L) := by
  set N : Subgroup G := normalizer ((F ⊔ zpowers z : Subgroup G) : Set G) with hN
  let _ : MulAction N G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp N.subtype)
  have hsmul : ∀ (c : N) (x : G), c • x = (c : G) * x * (c : G)⁻¹ := fun c x => rfl
  have horb : Nat.card (MulAction.orbit N z) = 16 := by
    rw [← D.F_card]
    symm
    refine Nat.card_congr (Equiv.ofBijective
      (fun f : F => (⟨z * f, ?_⟩ : MulAction.orbit N z)) ⟨?_, ?_⟩)
    · obtain ⟨c, hc, hcz⟩ := htrans f f.2
      exact ⟨⟨c, Subgroup.mem_normalizer_iff.2 hc⟩, (hsmul _ _).trans hcz⟩
    · intro f f' hff'
      exact Subtype.ext (mul_left_cancel (congrArg Subtype.val hff'))
    · rintro ⟨x, c, rfl⟩
      obtain ⟨f, hf, hcf⟩ := conj_z_mem h D (Subgroup.mem_normalizer_iff.1 c.2)
      refine ⟨⟨f, hf⟩, Subtype.ext ?_⟩
      show z * (f : G) = (c : G) * z * (c : G)⁻¹
      exact hcf.symm
  have hstab : Nat.card (MulAction.stabilizer N z) =
      Nat.card ↥(normalizer (F : Set G) ⊓ L) * 2 := by
    have hmap : (MulAction.stabilizer N z).map N.subtype =
        (normalizer (F : Set G) ⊓ L) ⊔ zpowers z := by
      rw [← N_inf_centralizer_eq h hZ D]
      ext x
      constructor
      · rintro ⟨c, hc, rfl⟩
        refine Subgroup.mem_inf.2 ⟨c.2, mem_centralizer_singleton_iff.2 ?_⟩
        have hc' : (c : G) * z * (c : G)⁻¹ = z := hc
        exact mul_inv_eq_iff_eq_mul.1 hc'
      · intro hx
        obtain ⟨hxN, hxC⟩ := Subgroup.mem_inf.1 hx
        refine ⟨⟨x, hxN⟩, ?_, rfl⟩
        have : x * z = z * x := mem_centralizer_singleton_iff.1 hxC
        show x * z * x⁻¹ = z
        rw [this]
        group
    rw [← card_sup_zpowers h (inf_le_right : normalizer (F : Set G) ⊓ L ≤ L), ← hmap,
      Subgroup.card_map_of_injective N.subtype_injective]
  have hkey := Subgroup.card_mul_index (MulAction.stabilizer N z)
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, horb, hstab] at hkey
  rw [← hkey]
  ring

theorem conj_mem_Ksub [Finite G] (h : OneClassData L z t) (D : NData L F) {b k : G} (hbL : b ∈ L)
    (hbF : ∀ x, x ∈ F ↔ b * x * b⁻¹ ∈ F) (hk : k ∈ Ksub z F) :
    b * k * b⁻¹ ∈ Ksub z F ∧ phiv z (b * k * b⁻¹) = b * phiv z k * b⁻¹ := by
  have hbz : b * z * b⁻¹ = z := by
    rw [← h.z_comm b hbL]
    group
  have hbz' : b⁻¹ * z * b = z := by
    have := h.z_comm b⁻¹ (Subgroup.inv_mem _ hbL)
    rw [← this]
    group
  have hbE : ∀ x, x ∈ F ⊔ zpowers z ↔ b * x * b⁻¹ ∈ F ⊔ zpowers z :=
    mem_normalizer_sup h D.F_le hbF (Subgroup.one_mem _) (by rw [hbz, mul_one])
  obtain ⟨hkE, hkF⟩ := mem_Ksub.1 hk
  refine ⟨mem_Ksub.2 ⟨fun x => ?_, fun f hf => ?_⟩, ?_⟩
  · have e1 := hbE (b⁻¹ * x * b)
    rw [show b * (b⁻¹ * x * b) * b⁻¹ = x by group] at e1
    have e2 := hkE (b⁻¹ * x * b)
    have e3 := hbE (k * (b⁻¹ * x * b) * k⁻¹)
    rw [show b * (k * (b⁻¹ * x * b) * k⁻¹) * b⁻¹ = b * k * b⁻¹ * x * (b * k * b⁻¹)⁻¹ by group]
      at e3
    exact e1.symm.trans (e2.trans e3)
  · have hf' : b⁻¹ * f * b ∈ F := by
      have e := hbF (b⁻¹ * f * b)
      rw [show b * (b⁻¹ * f * b) * b⁻¹ = f by group] at e
      exact e.2 hf
    have e := hkF (b⁻¹ * f * b) hf'
    calc f * (b * k * b⁻¹) = b * ((b⁻¹ * f * b) * k) * b⁻¹ := by group
      _ = b * (k * (b⁻¹ * f * b)) * b⁻¹ := by rw [e]
      _ = b * k * b⁻¹ * f := by group
  · unfold phiv
    calc z * (b * k * b⁻¹ * z * (b * k * b⁻¹)⁻¹)
        = z * (b * k * (b⁻¹ * z * b) * k⁻¹ * b⁻¹) := by group
      _ = z * (b * k * z * k⁻¹ * b⁻¹) := by rw [hbz']
      _ = (b * z * b⁻¹) * (b * (k * z * k⁻¹) * b⁻¹) := by rw [hbz]; group
      _ = b * (z * (k * z * k⁻¹)) * b⁻¹ := by group

theorem exists_Ksub_phiv_ne_one [Finite G] (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f) :
    ∃ k ∈ Ksub z F, phiv z k ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hKE : ∀ k ∈ Ksub z F, k ∈ F ⊔ zpowers z := fun k hk =>
    (phiv_eq_one_iff h D hk).1 (hcon k hk)
  set N : Subgroup G := normalizer ((F ⊔ zpowers z : Subgroup G) : Set G) with hN
  have hNF : N ≤ normalizer (F : Set G) := fun c hc =>
    Subgroup.mem_normalizer_iff.2 (normalizes_F h hZ D (Subgroup.mem_normalizer_iff.1 hc))
  let ρ : N →* MulAut F := F.normalizerMonoidHom.comp (Subgroup.inclusion hNF)
  have hker : ∀ c : N, c ∈ ρ.ker → (c : G) ∈ F ⊔ zpowers z := by
    intro c hc
    apply hKE
    refine mem_Ksub.2 ⟨Subgroup.mem_normalizer_iff.1 c.2, fun f hf => ?_⟩
    have h1 := congrArg (fun α : MulAut F => ((α ⟨f, hf⟩ : F) : G)) (MonoidHom.mem_ker.1 hc)
    have h2 : (c : G) * f * (c : G)⁻¹ = f := h1
    calc f * (c : G) = (c : G) * f * (c : G)⁻¹ * (c : G) := by rw [h2]
      _ = (c : G) * f := by group
  have hE : Nat.card (F ⊔ zpowers z : Subgroup G) = 32 := by
    rw [card_sup_zpowers h D.F_le, D.F_card]
  have hkerCard : Nat.card ρ.ker = 32 := by
    rw [← hE]
    refine Nat.card_congr (Equiv.ofBijective
      (fun c => (⟨(c.1 : G), hker c.1 c.2⟩ : (F ⊔ zpowers z : Subgroup G))) ⟨?_, ?_⟩)
    · intro c c' hcc'
      have h1 : ((c.1 : N) : G) = ((c'.1 : N) : G) :=
        congrArg (fun e : (F ⊔ zpowers z : Subgroup G) => (e : G)) hcc'
      exact Subtype.ext (Subtype.ext h1)
    · rintro ⟨e, he⟩
      have heN : e ∈ N := Subgroup.le_normalizer he
      refine ⟨⟨⟨e, heN⟩, ?_⟩, rfl⟩
      rw [MonoidHom.mem_ker]
      refine MulEquiv.ext fun f => Subtype.ext ?_
      show e * (f : G) * e⁻¹ = f
      rw [E_comm_F h D he f.2]
      group
  have hrange : Nat.card ρ.range ∣ 20160 := by
    rw [← card_mulEquiv_eq_of_elemAb16 (F := F)
      (fun x y => Subtype.ext (D.F_comm x x.2 y y.2)) (fun x => Subtype.ext (D.F_sq x x.2))
      D.F_card]
    exact Subgroup.card_subgroup_dvd_card ρ.range
  have hcard := Subgroup.card_ker_mul_card_range ρ
  have hN' := card_N h hZ D htrans
  rw [hkerCard, hN'] at hcard
  have hrng : Nat.card ρ.range = Nat.card ↥(normalizer (F : Set G) ⊓ L) :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 32) hcard
  have h128 : 128 ∣ Nat.card ρ.range := hrng ▸ D.N_two
  have := Nat.dvd_trans h128 hrange
  omega

theorem phiHom_surjective [Finite G] (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f) :
    Function.Surjective (phiHom h D) := by
  obtain ⟨k₀, hk₀, hk₀1⟩ := exists_Ksub_phiv_ne_one h hZ D htrans
  rintro ⟨f', hf'⟩
  by_cases hf'1 : f' = 1
  · exact ⟨1, by rw [map_one]; exact Subtype.ext hf'1.symm⟩
  · obtain ⟨b, hbL, hbF, hb⟩ := D.trans (phiv z k₀) (phiv_mem h D hk₀) hk₀1 f' hf' hf'1
    obtain ⟨hbk, hphi⟩ := conj_mem_Ksub h D hbL hbF hk₀
    refine ⟨⟨b * k₀ * b⁻¹, hbk⟩, Subtype.ext ?_⟩
    show phiv z (b * k₀ * b⁻¹) = f'
    rw [hphi, hb]

theorem ker_phiHom (h : OneClassData L z t) (D : NData L F) :
    (phiHom h D).ker = (F ⊔ zpowers z).subgroupOf (Ksub z F) := by
  ext k
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h1
    exact (phiv_eq_one_iff h D k.2).1 (congrArg Subtype.val h1)
  · intro h1
    exact Subtype.ext ((phiv_eq_one_iff h D k.2).2 h1)

theorem card_Ksub [Finite G] (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f) :
    Nat.card (Ksub z F) = 512 := by
  have h1 := Subgroup.card_ker_mul_card_range (phiHom h D)
  rw [(phiHom h D).range_eq_top_of_surjective (phiHom_surjective h hZ D htrans),
    Subgroup.card_top, ker_phiHom h D] at h1
  have h2 : Nat.card ((F ⊔ zpowers z).subgroupOf (Ksub z F)) = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (E_le_K h D)).toEquiv,
      card_sup_zpowers h D.F_le, D.F_card]
  rw [h2, D.F_card] at h1
  omega

end Main

end CFSG.EvenSporadicStandard.M23Std
