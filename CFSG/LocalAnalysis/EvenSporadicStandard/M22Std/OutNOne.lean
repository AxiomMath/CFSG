module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.NOne

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G]

structure OutOne (L : Subgroup G) (z : G) (F : Subgroup G) : Prop where
  z_mul_self : z * z = 1
  z_ne_one : z ≠ 1
  z_comm : ∀ l ∈ L, z * l = l * z
  z_not_mem : z ∉ L
  F_le : F ≤ L
  F_comm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x
  F_sq : ∀ x ∈ F, x * x = 1
  F_card : Nat.card F = 16
  not_conj : ∀ u ∈ F, u ≠ 1 → ¬ IsConj z u
  fused : ∀ f ∈ F, IsConj z (z * f)
  cent_F : ∀ k : G, k * z = z * k → (∀ f ∈ F, f * k = k * f) → k ∈ F ⊔ zpowers z
  trans : ∀ f ∈ F, f ≠ 1 → ∀ f' ∈ F, f' ≠ 1 →
    ∃ b ∈ L, (∀ x, x ∈ F ↔ b * x * b⁻¹ ∈ F) ∧ b * f * b⁻¹ = f'
  NH_two : 512 ∣ Nat.card ↥(normalizer ((F ⊔ zpowers z : Subgroup G) : Set G) ⊓
    centralizer ({z} : Set G))

variable {L : Subgroup G} {z : G} {F : Subgroup G}

namespace OutOne

variable (h : OutOne L z F)

include h in
theorem zpowers_le_cent {S : Subgroup G} (hS : S ≤ L) : zpowers z ≤ centralizer (S : Set G) :=
  zpowers_le.2 (mem_centralizer_iff.2 fun a ha => (h.z_comm a (hS ha)).symm)

include h in
theorem card_zpowers : Nat.card (zpowers z) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact h.z_mul_self) h.z_ne_one

include h in
theorem mem_zpowers_cases {b : G} (hb : b ∈ zpowers z) : b = 1 ∨ b = z :=
  mem_zpowers_involution h.z_mul_self hb

include h in
theorem disjoint_zpowers {S : Subgroup G} (hS : S ≤ L) : Disjoint S (zpowers z) := by
  rw [Subgroup.disjoint_def]
  intro x hxS hxz
  rcases h.mem_zpowers_cases hxz with rfl | rfl
  · rfl
  · exact absurd (hS hxS) h.z_not_mem

include h in
theorem card_sup_zpowers {S : Subgroup G} (hS : S ≤ L) :
    Nat.card (S ⊔ zpowers z : Subgroup G) = Nat.card S * 2 := by
  have e := mulEquivProdSup (A := S) (B := zpowers z) (h.zpowers_le_cent hS)
    (h.disjoint_zpowers hS)
  rw [← Nat.card_congr e.toEquiv, Nat.card_prod, h.card_zpowers]

include h in
theorem mem_mul_of_isConj {e : G} (he : e ∈ F ⊔ zpowers z) (hconj : IsConj z e) :
    ∃ f ∈ F, e = z * f := by
  obtain ⟨f, hf, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
    (h.zpowers_le_cent h.F_le) he
  rcases h.mem_zpowers_cases hb with rfl | rfl
  · exfalso
    rw [mul_one] at hconj
    by_cases hf1 : f = 1
    · subst hf1
      exact h.z_ne_one (isConj_one_right.1 hconj.symm)
    · exact h.not_conj f hf hf1 hconj
  · exact ⟨f, hf, (h.z_comm f (h.F_le hf)).symm⟩

include h in
theorem normalizes_F [Finite G] {c : G}
    (hc : ∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) :
    ∀ x, x ∈ F ↔ c * x * c⁻¹ ∈ F := by
  apply forall_mem_iff_of_forall_mem
  intro x hx
  have hxE : c * x * c⁻¹ ∈ F ⊔ zpowers z := (hc x).1 (Subgroup.mem_sup_left hx)
  obtain ⟨f, hf, b, hb, hfb⟩ := exists_mul_of_mem_sup_of_le_centralizer
    (h.zpowers_le_cent h.F_le) hxE
  rcases h.mem_zpowers_cases hb with hb1 | hbz
  · rw [hfb, hb1, mul_one]
    exact hf
  · exfalso
    rw [hbz] at hfb
    have h1 : IsConj z (c * x * c⁻¹) := by
      rw [hfb, ← h.z_comm f (h.F_le hf)]
      exact h.fused f hf
    have h2 : IsConj x (c * x * c⁻¹) := isConj_iff.2 ⟨c, rfl⟩
    have h3 : IsConj z x := h1.trans h2.symm
    by_cases hx1 : x = 1
    · subst hx1
      exact h.z_ne_one (isConj_one_right.1 h3.symm)
    · exact h.not_conj x hx hx1 h3

include h in
theorem mem_normalizer_sup [Finite G] {c s : G} (hcF : ∀ x, x ∈ F ↔ c * x * c⁻¹ ∈ F) (hs : s ∈ F)
    (hcz : c * z * c⁻¹ = z * s) :
    ∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z := by
  apply forall_mem_iff_of_forall_mem
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (h.zpowers_le_cent h.F_le) hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have h1 : c * (a * z ^ k) * c⁻¹ = (c * a * c⁻¹) * (z * s) ^ k := by
    rw [← hcz, conj_zpow]
    group
  rw [h1]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ((hcF a).1 ha)) ?_
  refine Subgroup.zpow_mem _ (Subgroup.mul_mem _ ?_ (Subgroup.mem_sup_left hs)) k
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)

include h in
theorem E_comm_F {e : G} (he : e ∈ F ⊔ zpowers z) {f : G} (hf : f ∈ F) : e * f = f * e := by
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (h.zpowers_le_cent h.F_le) he
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have h1 : Commute a f := h.F_comm a ha f hf
  have h2 : Commute (z ^ k) f := (show Commute z f from h.z_comm f (h.F_le hf)).zpow_left k
  exact (h1.mul_left h2).eq

include h in
theorem E_le_K : F ⊔ zpowers z ≤ Ksub z F := by
  intro e he
  rw [mem_Ksub]
  refine ⟨fun x => ?_, fun f hf => (h.E_comm_F he hf).symm⟩
  have := (Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer he) x)
  exact this

include h in
theorem conj_z_mem {k : G} (hk : ∀ x, x ∈ F ⊔ zpowers z ↔ k * x * k⁻¹ ∈ F ⊔ zpowers z) :
    ∃ f ∈ F, k * z * k⁻¹ = z * f := by
  refine h.mem_mul_of_isConj ((hk z).1 (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))) ?_
  exact (isConj_iff.2 ⟨k, rfl⟩ : IsConj z (k * z * k⁻¹))

include h in
theorem phiv_mem {k : G} (hk : k ∈ Ksub z F) : phiv z k ∈ F := by
  obtain ⟨f, hf, hkf⟩ := h.conj_z_mem (mem_Ksub.1 hk).1
  unfold phiv
  rw [hkf, ← mul_assoc, h.z_mul_self, one_mul]
  exact hf

include h in
theorem phiv_mul {k k' : G} (hk : k ∈ Ksub z F) (hk' : k' ∈ Ksub z F) :
    phiv z (k * k') = phiv z k * phiv z k' := by
  have hpF : phiv z k' ∈ F := h.phiv_mem hk'
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

@[expose] def phiHomO (h : OutOne L z F) : Ksub z F →* F :=
  MonoidHom.mk' (fun k => ⟨phiv z k, h.phiv_mem k.2⟩) (fun k k' =>
    Subtype.ext (h.phiv_mul k.2 k'.2))

include h in
theorem phiv_eq_one_iff {k : G} (hk : k ∈ Ksub z F) : phiv z k = 1 ↔ k ∈ F ⊔ zpowers z := by
  constructor
  · intro h1
    have hkz : k * z * k⁻¹ = z := by
      unfold phiv at h1
      rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right h.z_mul_self]
    have hkz' : k * z = z * k := mul_inv_eq_iff_eq_mul.1 hkz
    exact h.cent_F k hkz' (fun f hf => ((mem_Ksub.1 hk).2 f hf))
  · intro he
    obtain ⟨f, hf, b, hb, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_centralizer (h.zpowers_le_cent h.F_le) he
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hfz : Commute f z := (h.z_comm f (h.F_le hf)).symm
    have hbz : Commute (z ^ j) z := (Commute.refl z).zpow_left j
    have hkz : f * z ^ j * z = z * (f * z ^ j) := (hfz.mul_left hbz).eq
    unfold phiv
    rw [hkz]
    calc z * (z * (f * z ^ j) * (f * z ^ j)⁻¹) = (z * z) * (f * z ^ j * (f * z ^ j)⁻¹) := by
          simp only [mul_assoc]
      _ = 1 := by rw [h.z_mul_self]; group

include h in
theorem card_N [Finite G]
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f) :
    Nat.card ↥(normalizer ((F ⊔ zpowers z : Subgroup G) : Set G)) =
      16 * Nat.card ↥(normalizer ((F ⊔ zpowers z : Subgroup G) : Set G) ⊓
        centralizer ({z} : Set G)) := by
  set N : Subgroup G := normalizer ((F ⊔ zpowers z : Subgroup G) : Set G) with hN
  let _ : MulAction N G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp N.subtype)
  have hsmul : ∀ (c : N) (x : G), c • x = (c : G) * x * (c : G)⁻¹ := fun c x => rfl
  have horb : Nat.card (MulAction.orbit N z) = 16 := by
    rw [← h.F_card]
    symm
    refine Nat.card_congr (Equiv.ofBijective
      (fun f : F => (⟨z * f, ?_⟩ : MulAction.orbit N z)) ⟨?_, ?_⟩)
    · obtain ⟨c, hc, hcz⟩ := htrans f f.2
      exact ⟨⟨c, Subgroup.mem_normalizer_iff.2 hc⟩, (hsmul _ _).trans hcz⟩
    · intro f f' hff'
      exact Subtype.ext (mul_left_cancel (congrArg Subtype.val hff'))
    · rintro ⟨x, c, rfl⟩
      obtain ⟨f, hf, hcf⟩ := h.conj_z_mem (Subgroup.mem_normalizer_iff.1 c.2)
      refine ⟨⟨f, hf⟩, Subtype.ext ?_⟩
      show z * (f : G) = (c : G) * z * (c : G)⁻¹
      exact hcf.symm
  have hmap : (MulAction.stabilizer N z).map N.subtype = N ⊓ centralizer ({z} : Set G) := by
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
  have hstab : Nat.card (MulAction.stabilizer N z) = Nat.card ↥(N ⊓ centralizer ({z} : Set G)) := by
    rw [← hmap, Subgroup.card_map_of_injective N.subtype_injective]
  have hkey := Subgroup.card_mul_index (MulAction.stabilizer N z)
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, horb, hstab] at hkey
  rw [← hkey]
  ring

include h in
theorem conj_mem_Ksub [Finite G] {b k : G} (hbL : b ∈ L)
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
    h.mem_normalizer_sup hbF (Subgroup.one_mem _) (by rw [hbz, mul_one])
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

include h in
theorem exists_Ksub_phiv_ne_one [Finite G]
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f) :
    ∃ k ∈ Ksub z F, phiv z k ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hKE : ∀ k ∈ Ksub z F, k ∈ F ⊔ zpowers z := fun k hk =>
    (h.phiv_eq_one_iff hk).1 (hcon k hk)
  set N : Subgroup G := normalizer ((F ⊔ zpowers z : Subgroup G) : Set G) with hN
  have hNF : N ≤ normalizer (F : Set G) := fun c hc =>
    Subgroup.mem_normalizer_iff.2 (h.normalizes_F (Subgroup.mem_normalizer_iff.1 hc))
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
    rw [h.card_sup_zpowers h.F_le, h.F_card]
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
      rw [h.E_comm_F he f.2]
      group
  have hrange : Nat.card ρ.range ∣ 20160 := by
    rw [← card_mulEquiv_eq_of_elemAb16 (F := F)
      (fun x y => Subtype.ext (h.F_comm x x.2 y y.2)) (fun x => Subtype.ext (h.F_sq x x.2))
      h.F_card]
    exact Subgroup.card_subgroup_dvd_card ρ.range
  have hcard := Subgroup.card_ker_mul_card_range ρ
  have hN' := h.card_N htrans
  have h8192 : 8192 ∣ Nat.card N := by
    rw [hN']
    exact Nat.mul_dvd_mul_left 16 h.NH_two |>.trans (by norm_num)
  rw [hkerCard] at hcard
  have h256 : 256 ∣ Nat.card ρ.range := by
    have : 32 * 256 ∣ 32 * Nat.card ρ.range := by
      rw [hcard]
      exact h8192
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have := Nat.dvd_trans h256 hrange
  omega

include h in
theorem phiHomO_surjective [Finite G]
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f) :
    Function.Surjective (phiHomO h) := by
  obtain ⟨k₀, hk₀, hk₀1⟩ := h.exists_Ksub_phiv_ne_one htrans
  rintro ⟨f', hf'⟩
  by_cases hf'1 : f' = 1
  · exact ⟨1, by rw [map_one]; exact Subtype.ext hf'1.symm⟩
  · obtain ⟨b, hbL, hbF, hb⟩ := h.trans (phiv z k₀) (h.phiv_mem hk₀) hk₀1 f' hf' hf'1
    obtain ⟨hbk, hphi⟩ := h.conj_mem_Ksub hbL hbF hk₀
    refine ⟨⟨b * k₀ * b⁻¹, hbk⟩, Subtype.ext ?_⟩
    show phiv z (b * k₀ * b⁻¹) = f'
    rw [hphi, hb]

include h in
theorem ker_phiHomO : (phiHomO h).ker = (F ⊔ zpowers z).subgroupOf (Ksub z F) := by
  ext k
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h1
    exact (h.phiv_eq_one_iff k.2).1 (congrArg Subtype.val h1)
  · intro h1
    exact Subtype.ext ((h.phiv_eq_one_iff k.2).2 h1)

include h in
theorem card_Ksub [Finite G]
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f) :
    Nat.card (Ksub z F) = 512 := by
  have h1 := Subgroup.card_ker_mul_card_range (phiHomO h)
  rw [(phiHomO h).range_eq_top_of_surjective (h.phiHomO_surjective htrans),
    Subgroup.card_top, h.ker_phiHomO] at h1
  have h2 : Nat.card ((F ⊔ zpowers z).subgroupOf (Ksub z F)) = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E_le_K).toEquiv,
      h.card_sup_zpowers h.F_le, h.F_card]
  rw [h2, h.F_card] at h1
  omega

include h in
theorem center_Ksub [Finite G]
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f) {x : G} (hx : x ∈ Ksub z F) :
    (∀ k ∈ Ksub z F, x * k = k * x) ↔ x ∈ F := by
  constructor
  · intro hcent
    have hzK : z ∈ Ksub z F := h.E_le_K (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
    have hxz : phiv z x = 1 := by
      unfold phiv
      have := hcent z hzK
      rw [show x * z * x⁻¹ = z by rw [this]; group, h.z_mul_self]
    have hxE := (h.phiv_eq_one_iff hx).1 hxz
    obtain ⟨f, hf, b, hb, hxfb⟩ :=
      exists_mul_of_mem_sup_of_le_centralizer (h.zpowers_le_cent h.F_le) hxE
    rcases h.mem_zpowers_cases hb with hb1 | hbz
    · rw [hxfb, hb1, mul_one]
      exact hf
    · exfalso
      obtain ⟨k₀, hk₀, hk₀1⟩ := h.exists_Ksub_phiv_ne_one htrans
      apply hk₀1
      have h1 := hcent k₀ hk₀
      rw [hxfb, hbz] at h1
      have h2 : k₀ * f = f * k₀ := ((mem_Ksub.1 hk₀).2 f hf).symm
      have h4 : k₀ * (f * z) * k₀⁻¹ = f * z := by
        rw [← h1]
        group
      have h3 : k₀ * z * k₀⁻¹ = z := by
        calc k₀ * z * k₀⁻¹ = f⁻¹ * (f * k₀ * z * k₀⁻¹) := by group
          _ = f⁻¹ * (k₀ * f * z * k₀⁻¹) := by rw [← h2]
          _ = f⁻¹ * (k₀ * (f * z) * k₀⁻¹) := by group
          _ = f⁻¹ * (f * z) := by rw [h4]
          _ = z := by group
      unfold phiv
      rw [h3, h.z_mul_self]
  · intro hxF k hk
    exact (mem_Ksub.1 hk).2 x hxF

end OutOne

end CFSG.EvenSporadicStandard.M22Std
