module

public import Mathlib.GroupTheory.PGroup
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.GroupTheory.ONan

open MulAction Subgroup

private lemma onanB_map_conj {X : Type} {Ω : Type*} [Group X] [MulAction X Ω]
    (K : Ω → Ω → Subgroup X)
    (hKconj : ∀ (g : X) (u v : Ω) (k : X), k ∈ K u v ↔ g * k * g⁻¹ ∈ K (g • u) (g • v))
    (g : X) (u v : Ω) :
    (K u v).map (MulAut.conj g) = K (g • u) (g • v) := by
  ext k
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using (hKconj g u v y).mp hy
  · intro hk
    refine ⟨g⁻¹ * k * g, ?_, ?_⟩
    · simpa using (hKconj g⁻¹ (g • u) (g • v) k).mp hk
    · simp [MulAut.conj_apply, mul_assoc]

private lemma onanB_mem_normalizer_of_fixed {X : Type} {Ω : Type*} [Group X] [MulAction X Ω]
    (K : Ω → Ω → Subgroup X)
    (hKconj : ∀ (g : X) (u v : Ω) (k : X), k ∈ K u v ↔ g * k * g⁻¹ ∈ K (g • u) (g • v))
    {g : X} {u v : Ω} (hu : g • u = u) (hv : g • v = v) :
    g ∈ Subgroup.normalizer (K u v : Set X) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, onanB_map_conj K hKconj g u v, hu, hv]

theorem natCard_eq_natCard {X : Type} {Ω : Type*} [Group X] [MulAction X Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d)
    (K : Ω → Ω → Subgroup X)
    (hKconj : ∀ (g : X) (u v : Ω) (k : X), k ∈ K u v ↔ g * k * g⁻¹ ∈ K (g • u) (g • v))
    {u v u' v' : Ω} (huv : u ≠ v) (huv' : u' ≠ v') :
    Nat.card (K u v) = Nat.card (K u' v') := by
  obtain ⟨g, hgu, hgv⟩ := h2 u v u' v' huv huv'
  have hmap : (K u v).map (MulAut.conj g) = K u' v' := by
    rw [onanB_map_conj K hKconj g u v, hgu, hgv]
  rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]

private lemma onanB_eq_of_le_natCard {X : Type} {Ω : Type*} [Group X] [Finite X]
    [MulAction X Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d)
    (K : Ω → Ω → Subgroup X)
    (hKconj : ∀ (g : X) (u v : Ω) (k : X), k ∈ K u v ↔ g * k * g⁻¹ ∈ K (g • u) (g • v))
    {u v u' v' : Ω} (huv : u ≠ v) (huv' : u' ≠ v') (hle : K u v ≤ K u' v') :
    K u v = K u' v' := by
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  exact (natCard_eq_natCard h2 K hKconj huv huv').ge

private lemma onanB_normalizer_le_stabilizer {X : Type} {Ω : Type*} [Group X] [Finite X]
    [MulAction X Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d)
    (K : Ω → Ω → Subgroup X)
    (hKfix : ∀ u v, u ≠ v → ∀ k ∈ K u v, k • u = u ∧ k • v = v)
    (hKconj : ∀ (g : X) (u v : Ω) (k : X), k ∈ K u v ↔ g * k * g⁻¹ ∈ K (g • u) (g • v))
    (hKsc : ∀ u v w, u ≠ v → u ≠ w → v ≠ w → ∀ k ∈ K u v, k • w = w → k ∈ K u w)
    {u v : Ω} (huv : u ≠ v) (hnot : ¬ K u v ≤ K v u) :
    Subgroup.normalizer (K u v : Set X) ≤ stabilizer X u := by
  intro f hf
  rw [MulAction.mem_stabilizer_iff]
  by_contra hfu
  have hT : K (f • u) (f • v) = K u v := by
    rw [← onanB_map_conj K hKconj f u v]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hf
  have hfuv : f • u ≠ f • v := (MulAction.injective f).ne huv
  have hT1 : K u v ≤ K u (f • u) := by
    by_cases hvu : f • u = v
    · rw [hvu]
    · intro k hk
      have hk' : k ∈ K (f • u) (f • v) := by rwa [hT]
      exact hKsc u v (f • u) huv (fun h => hfu h.symm) (fun h => hvu h.symm) k hk
        (hKfix (f • u) (f • v) hfuv k hk').1
  have hT2 : K u v ≤ K (f • u) u := by
    by_cases hvf : f • v = u
    · rw [← hT, hvf]
    · intro k hk
      have hk' : k ∈ K (f • u) (f • v) := by rwa [hT]
      exact hKsc (f • u) (f • v) u hfuv hfu hvf k hk' (hKfix u v huv k hk).1
  have hEq1 : K u v = K u (f • u) :=
    onanB_eq_of_le_natCard h2 K hKconj huv (fun h => hfu h.symm) hT1
  have hEq2 : K u v = K (f • u) u :=
    onanB_eq_of_le_natCard h2 K hKconj huv hfu hT2
  obtain ⟨g, hgu, hgv⟩ := h2 u (f • u) u v (fun h => hfu h.symm) huv
  have hcontra : K u v = K v u := by
    calc K u v = (K u (f • u)).map (MulAut.conj g) := by
          rw [onanB_map_conj K hKconj g u (f • u), hgu, hgv]
      _ = (K (f • u) u).map (MulAut.conj g) := by rw [← hEq1, hEq2]
      _ = K v u := by
          rw [onanB_map_conj K hKconj g (f • u) u, hgu, hgv]
  exact hnot hcontra.le

theorem eq_of_fixed {X : Type} {Ω : Type*} [Group X] [Finite X] [MulAction X Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d)
    (K : Ω → Ω → Subgroup X)
    (hKconj : ∀ (g : X) (u v : Ω) (k : X), k ∈ K u v ↔ g * k * g⁻¹ ∈ K (g • u) (g • v))
    (hKsc : ∀ u v w, u ≠ v → u ≠ w → v ≠ w → ∀ k ∈ K u v, k • w = w → k ∈ K u w)
    {u v w : Ω} (huv : u ≠ v) (hwu : w ≠ u) (hw : ∀ k ∈ K u v, k • w = w) :
    K u w = K u v := by
  by_cases hwv : w = v
  · subst w
    rfl
  · have hle : K u v ≤ K u w := fun k hk =>
      hKsc u v w huv hwu.symm (fun h => hwv h.symm) k hk (hw k hk)
    exact (onanB_eq_of_le_natCard h2 K hKconj huv hwu.symm hle).symm

private lemma onanB_inf_eq {X : Type} {Ω : Type*} [Group X] [MulAction X Ω]
    (K : Ω → Ω → Subgroup X)
    (hKfix : ∀ u v, u ≠ v → ∀ k ∈ K u v, k • u = u ∧ k • v = v)
    (hKsc : ∀ u v w, u ≠ v → u ≠ w → v ≠ w → ∀ k ∈ K u v, k • w = w → k ∈ K u w)
    {x y z : Ω} (hxy : x ≠ y) (hxz : x ≠ z) (hzy : z ≠ y)
    (hz : ∀ k ∈ K y x, k • z = z) :
    K y x ⊓ K x z = K x y ⊓ K y x := by
  ext k
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨hkyx, hkxz⟩
    exact ⟨hKsc x z y hxz hxy hzy k hkxz (hKfix y x hxy.symm k hkyx).1, hkyx⟩
  · rintro ⟨hkxy, hkyx⟩
    exact ⟨hkyx, hKsc x y z hxy hxz hzy.symm k hkxy (hz k hkyx)⟩

private lemma onanB_card_sup_eq {X : Type} {Ω : Type*} [Group X] [Finite X]
    [MulAction X Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d)
    (K : Ω → Ω → Subgroup X)
    (hKfix : ∀ u v, u ≠ v → ∀ k ∈ K u v, k • u = u ∧ k • v = v)
    (hKconj : ∀ (g : X) (u v : Ω) (k : X), k ∈ K u v ↔ g * k * g⁻¹ ∈ K (g • u) (g • v))
    (hKsc : ∀ u v w, u ≠ v → u ≠ w → v ≠ w → ∀ k ∈ K u v, k • w = w → k ∈ K u w)
    {x y z : Ω} (hxy : x ≠ y) (hxz : x ≠ z) (hzy : z ≠ y)
    (hz : ∀ k ∈ K y x, k • z = z) :
    Nat.card ↥(K y x ⊔ K x z) = Nat.card ↥(K x y ⊔ K y x) := by
  have hPnormQ : K y x ≤ Subgroup.normalizer (K x z : Set X) := fun k hk =>
    onanB_mem_normalizer_of_fixed K hKconj (hKfix y x hxy.symm k hk).2 (hz k hk)
  have hKnorm : K y x ≤ Subgroup.normalizer (K x y : Set X) := fun k hk =>
    onanB_mem_normalizer_of_fixed K hKconj (hKfix y x hxy.symm k hk).2 (hKfix y x hxy.symm k hk).1
  have h1 := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (G := X) (H := K y x) (K := K x z) hPnormQ
  have h2' := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (G := X) (H := K y x) (K := K x y) hKnorm
  have hinf := onanB_inf_eq K hKfix hKsc hxy hxz hzy hz
  have hcard : Nat.card (K x z) = Nat.card (K x y) :=
    natCard_eq_natCard h2 K hKconj hxz hxy
  have hpos : 0 < Nat.card ↥(K y x ⊓ K x z) := by
    haveI : Nonempty ↥(K y x ⊓ K x z) := ⟨⟨1, by simp⟩⟩
    exact Nat.card_pos
  refine Nat.mul_right_cancel hpos ?_
  rw [h1, hcard, ← h2', sup_comm (K y x) (K x y), inf_comm (K y x) (K x y), hinf]

private lemma onanB_inf_stabilizer_le {X : Type} {Ω : Type*} [Group X] [MulAction X Ω]
    (K : Ω → Ω → Subgroup X)
    (hKconj : ∀ (g : X) (u v : Ω) (k : X), k ∈ K u v ↔ g * k * g⁻¹ ∈ K (g • u) (g • v))
    (hKfix : ∀ u v, u ≠ v → ∀ k ∈ K u v, k • u = u ∧ k • v = v)
    {x y z : Ω} (hxz : x ≠ z) :
    K x z ⊓ stabilizer X y ≤ K x z ⊓ Subgroup.normalizer (K y x : Set X) := by
  intro b hb
  rw [Subgroup.mem_inf] at hb ⊢
  refine ⟨hb.1, ?_⟩
  have hby : b • y = y := MulAction.mem_stabilizer_iff.mp hb.2
  have hbx : b • x = x := (hKfix x z hxz b hb.1).1
  exact onanB_mem_normalizer_of_fixed K hKconj hby hbx

private lemma onanB_exists_conj_witness {X : Type} [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime] {P Q R : Subgroup X}
    (hP : IsPGroup p P) (hQ : IsPGroup p Q)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set X))
    (hlt : P ⊔ R < P ⊔ Q) :
    ∃ f : X, f ∈ P ⊔ Q ∧ f ∉ P ⊔ R ∧
      (∀ h ∈ P ⊔ R, f * h * f⁻¹ ∈ P ⊔ R) ∧
      (∀ h ∈ P ⊔ R, f⁻¹ * h * f ∈ P ⊔ R) := by
  have hHp : IsPGroup p ↥(P ⊔ Q) := by
    have h := IsPGroup.to_sup_of_normal_left' hQ hP hPQ
    rwa [sup_comm] at h
  haveI : Group.IsNilpotent ↥(P ⊔ Q) := hHp.isNilpotent
  have hPRle : P ⊔ R ≤ P ⊔ Q := by
    rw [sup_le_iff]
    exact ⟨le_sup_left, le_trans le_sup_right hlt.le⟩
  have hSlt : (P ⊔ R).subgroupOf (P ⊔ Q) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hlt.ne (le_antisymm hlt.le htop)
  obtain ⟨u, huN, huS⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent ((P ⊔ R).subgroupOf (P ⊔ Q)) hSlt)
  have hconj : ∀ h ∈ P ⊔ R, (u : X) * h * (u : X)⁻¹ ∈ P ⊔ R := by
    intro h hh
    have hhH : (⟨h, hPRle hh⟩ : ↥(P ⊔ Q)) ∈ (P ⊔ R).subgroupOf (P ⊔ Q) :=
      Subgroup.mem_subgroupOf.mpr hh
    have hmem := (Subgroup.mem_normalizer_iff.mp huN ⟨h, hPRle hh⟩).mp hhH
    simpa using Subgroup.mem_subgroupOf.mp hmem
  have hconjInv : ∀ h ∈ P ⊔ R, (u : X)⁻¹ * h * (u : X) ∈ P ⊔ R := by
    intro h hh
    have hhH : (⟨h, hPRle hh⟩ : ↥(P ⊔ Q)) ∈ (P ⊔ R).subgroupOf (P ⊔ Q) :=
      Subgroup.mem_subgroupOf.mpr hh
    have huN' : (u : ↥(P ⊔ Q))⁻¹ ∈
        Subgroup.normalizer ((P ⊔ R).subgroupOf (P ⊔ Q) : Set ↥(P ⊔ Q)) :=
      Subgroup.inv_mem _ huN
    have hmem := (Subgroup.mem_normalizer_iff.mp huN' ⟨h, hPRle hh⟩).mp hhH
    simpa using Subgroup.mem_subgroupOf.mp hmem
  exact ⟨(u : X), u.2, fun h => huS (Subgroup.mem_subgroupOf.mpr h), hconj, hconjInv⟩

private lemma onanB_le_normalizer_map_conj {X : Type} [Group X]
    {P R : Subgroup X} {f : X} (hPR : ∀ h ∈ P ⊔ R, f⁻¹ * h * f ∈ P ⊔ R)
    (hR : R ≤ Subgroup.normalizer (P : Set X)) :
    P ≤ Subgroup.normalizer
      ((P.map (MulAut.conj f).toMonoidHom : Subgroup X) : Set X) := by
  have hPRnorm : P ⊔ R ≤ Subgroup.normalizer (P : Set X) := sup_le Subgroup.le_normalizer hR
  intro p hp
  have hpPR : p ∈ P ⊔ R := Subgroup.mem_sup_left hp
  have hg : f⁻¹ * p * f ∈ Subgroup.normalizer (P : Set X) := hPRnorm (hPR p hpPR)
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    obtain ⟨p0, hp0, hp0eq⟩ := Subgroup.mem_map.mp hq
    change (MulAut.conj f).toMonoidHom p0 = q at hp0eq
    have hmem : (f⁻¹ * p * f) * p0 * (f⁻¹ * p * f)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hg p0).mp hp0
    refine Subgroup.mem_map.mpr ⟨_, hmem, ?_⟩
    rw [← hp0eq]
    have hiden : (MulAut.conj f).toMonoidHom
        ((f⁻¹ * p * f) * p0 * (f⁻¹ * p * f)⁻¹) =
        p * (MulAut.conj f).toMonoidHom p0 * p⁻¹ := by
      change f * ((f⁻¹ * p * f) * p0 * (f⁻¹ * p * f)⁻¹) * f⁻¹ =
        p * (f * p0 * f⁻¹) * p⁻¹
      group
    exact hiden
  · intro hq
    obtain ⟨p0, hp0, hp0eq⟩ := Subgroup.mem_map.mp hq
    change (MulAut.conj f).toMonoidHom p0 = p * q * p⁻¹ at hp0eq
    have hginv : (f⁻¹ * p * f)⁻¹ ∈ Subgroup.normalizer (P : Set X) := Subgroup.inv_mem _ hg
    have hmem : (f⁻¹ * p * f)⁻¹ * p0 * (f⁻¹ * p * f) ∈ P := by
      simpa using (Subgroup.mem_normalizer_iff.mp hginv p0).mp hp0
    refine Subgroup.mem_map.mpr ⟨_, hmem, ?_⟩
    have hqeq : q = p⁻¹ * (MulAut.conj f).toMonoidHom p0 * p := by
      rw [hp0eq]
      group
    rw [hqeq]
    have hiden : (MulAut.conj f).toMonoidHom
        ((f⁻¹ * p * f)⁻¹ * p0 * (f⁻¹ * p * f)) =
        p⁻¹ * (MulAut.conj f).toMonoidHom p0 * p := by
      change f * ((f⁻¹ * p * f)⁻¹ * p0 * (f⁻¹ * p * f)) * f⁻¹ =
        p⁻¹ * (f * p0 * f⁻¹) * p
      group
    exact hiden

private lemma onanB_card_sup_comm {X : Type} {Ω : Type*} [Group X] [MulAction X Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d)
    (K : Ω → Ω → Subgroup X)
    (hKconj : ∀ (g : X) (u v : Ω) (k : X), k ∈ K u v ↔ g * k * g⁻¹ ∈ K (g • u) (g • v))
    {u v u' v' : Ω} (huv : u ≠ v) (huv' : u' ≠ v') :
    Nat.card ↥(K u v ⊔ K v u) = Nat.card ↥(K u' v' ⊔ K v' u') := by
  obtain ⟨g, hgu, hgv⟩ := h2 u v u' v' huv huv'
  have h1 : (K u v).map (MulAut.conj g).toMonoidHom = K u' v' := by
    change (K u v).map (MulAut.conj g) = K u' v'
    rw [onanB_map_conj K hKconj g u v, hgu, hgv]
  have h2' : (K v u).map (MulAut.conj g).toMonoidHom = K v' u' := by
    change (K v u).map (MulAut.conj g) = K v' u'
    rw [onanB_map_conj K hKconj g v u, hgu, hgv]
  calc Nat.card ↥(K u v ⊔ K v u)
      = Nat.card ↥((K u v ⊔ K v u).map (MulAut.conj g).toMonoidHom) := by
        rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    _ = Nat.card ↥((K u v).map (MulAut.conj g).toMonoidHom ⊔
          (K v u).map (MulAut.conj g).toMonoidHom) := by
        rw [Subgroup.map_sup (K u v) (K v u) (MulAut.conj g).toMonoidHom]
    _ = Nat.card ↥(K u' v' ⊔ K v' u') := by rw [h1, h2']

private lemma onanB_sup_lt_sup {X : Type} [Group X] {P Q R : Subgroup X}
    (hR : R ≤ Subgroup.normalizer (P : Set X)) (hRQ : R ≤ Q) (hne : R ≠ Q)
    (hReq : R = Q ⊓ Subgroup.normalizer (P : Set X)) :
    P ⊔ R < P ⊔ Q := by
  have hle : P ⊔ R ≤ P ⊔ Q := sup_le_sup_left hRQ P
  refine lt_of_le_of_ne hle ?_
  intro heq
  apply hne
  have hQle : Q ≤ P ⊔ R := by
    rw [heq]
    exact le_sup_right
  have hPRnorm : P ⊔ R ≤ Subgroup.normalizer (P : Set X) :=
    sup_le Subgroup.le_normalizer hR
  have hQR : Q ≤ R := by
    rw [hReq]
    exact le_inf le_rfl (le_trans hQle hPRnorm)
  exact le_antisymm hRQ hQR

private lemma onanB_sup_fixes_x {X : Type} {Ω : Type*} [Group X] [MulAction X Ω]
    (K : Ω → Ω → Subgroup X)
    (hKfix : ∀ u v, u ≠ v → ∀ k ∈ K u v, k • u = u ∧ k • v = v)
    {x y z : Ω} (hxy : x ≠ y) (hxz : x ≠ z) {f : X}
    (hfH : f ∈ K y x ⊔ K x z) : f • x = x := by
  have hstab : K y x ⊔ K x z ≤ stabilizer X x :=
    sup_le (fun k hk => (hKfix y x hxy.symm k hk).2)
      (fun k hk => (hKfix x z hxz k hk).1)
  exact MulAction.mem_stabilizer_iff.mp (hstab hfH)

private lemma onanB_witness_moves_y {X : Type} {Ω : Type*} [Group X] [MulAction X Ω]
    (K : Ω → Ω → Subgroup X)
    (hKconj : ∀ (g : X) (u v : Ω) (k : X), k ∈ K u v ↔ g * k * g⁻¹ ∈ K (g • u) (g • v))
    (hKfix : ∀ u v, u ≠ v → ∀ k ∈ K u v, k • u = u ∧ k • v = v)
    {x y z : Ω} (hxy : x ≠ y) (hxz : x ≠ z)
    (hPQ : K y x ≤ Subgroup.normalizer (K x z : Set X))
    {f : X} (hfH : f ∈ K y x ⊔ K x z)
    (hfR : f ∉ K y x ⊔ (K x z ⊓ Subgroup.normalizer (K y x : Set X))) :
    f • y ≠ y := by
  intro hfy
  have hfmul := Subgroup.coe_mul_of_left_le_normalizer_right (K y x) (K x z) hPQ
  have hfmem : f ∈ (↑(K y x ⊔ K x z) : Set X) := hfH
  rw [hfmul] at hfmem
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hfmem
  have hay : a • y = y := (hKfix y x hxy.symm a ha).1
  have hby : b • y = y := by
    have h : a • (b • y) = a • y := by
      rw [← mul_smul, hab, hfy, hay]
    exact MulAction.injective a h
  have hbR : b ∈ K x z ⊓ Subgroup.normalizer (K y x : Set X) := by
    exact onanB_inf_stabilizer_le K hKconj hKfix hxz
      ⟨hb, MulAction.mem_stabilizer_iff.mpr hby⟩
  apply hfR
  have haPR : a ∈ K y x ⊔ (K x z ⊓ Subgroup.normalizer (K y x : Set X)) :=
    Subgroup.mem_sup_left ha
  have hbPR : b ∈ K y x ⊔ (K x z ⊓ Subgroup.normalizer (K y x : Set X)) :=
    Subgroup.mem_sup_right hbR
  rw [← hab]
  exact mul_mem haPR hbPR

private lemma onanB_eq_Kyy' {X : Type} {Ω : Type*} [Group X] [Finite X] [MulAction X Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d)
    (K : Ω → Ω → Subgroup X)
    (hKconj : ∀ (g : X) (u v : Ω) (k : X), k ∈ K u v ↔ g * k * g⁻¹ ∈ K (g • u) (g • v))
    (hKsc : ∀ u v w, u ≠ v → u ≠ w → v ≠ w → ∀ k ∈ K u v, k • w = w → k ∈ K u w)
    {x y : Ω} (hxy : x ≠ y) {f : X} (hy' : f • y ≠ y) (hy'x : f • y ≠ x)
    (hfix : K y x ≤ stabilizer X (f • y)) :
    K y x = K y (f • y) := by
  have hle : K y x ≤ K y (f • y) := fun k hk =>
    hKsc y x (f • y) hxy.symm hy'.symm hy'x.symm k hk
      (MulAction.mem_stabilizer_iff.mp (hfix hk))
  exact onanB_eq_of_le_natCard h2 K hKconj hxy.symm hy'.symm hle

private lemma onanB_eq_P' {X : Type} {Ω : Type*} [Group X] [Finite X] [MulAction X Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d)
    (K : Ω → Ω → Subgroup X)
    (hKconj : ∀ (g : X) (u v : Ω) (k : X), k ∈ K u v ↔ g * k * g⁻¹ ∈ K (g • u) (g • v))
    (hKsc : ∀ u v w, u ≠ v → u ≠ w → v ≠ w → ∀ k ∈ K u v, k • w = w → k ∈ K u w)
    {x y : Ω} (hxy : x ≠ y) {f : X} (hy'x : f • y ≠ x) (hy'y : f • y ≠ y)
    (hP'K : (K y x).map (MulAut.conj f).toMonoidHom = K (f • y) x)
    (hfix : (K y x).map (MulAut.conj f).toMonoidHom ≤ stabilizer X y) :
    (K y x).map (MulAut.conj f).toMonoidHom = K (f • y) y := by
  have hle : (K y x).map (MulAut.conj f).toMonoidHom ≤ K (f • y) y := by
    intro q hq
    have hq' : q ∈ K (f • y) x := by rwa [hP'K] at hq
    exact hKsc (f • y) x y hy'x hy'y hxy q hq'
      (MulAction.mem_stabilizer_iff.mp (hfix hq))
  rw [hP'K] at hle ⊢
  exact onanB_eq_of_le_natCard h2 K hKconj hy'x hy'y hle

private lemma onanB_card_contradiction {X : Type} {Ω : Type*} [Group X] [Finite X]
    [MulAction X Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d)
    (K : Ω → Ω → Subgroup X)
    (hKconj : ∀ (g : X) (u v : Ω) (k : X), k ∈ K u v ↔ g * k * g⁻¹ ∈ K (g • u) (g • v))
    {x y z : Ω} (hxy : x ≠ y) {f : X} (hy'y : f • y ≠ y) {P' : Subgroup X}
    (hPeq : K y x = K y (f • y)) (hP'eq : P' = K (f • y) y)
    (hP'le : P' ≤ K y x ⊔ (K x z ⊓ Subgroup.normalizer (K y x : Set X)))
    (hsupRlt : K y x ⊔ (K x z ⊓ Subgroup.normalizer (K y x : Set X)) < K y x ⊔ K x z)
    (hcardd : Nat.card ↥(K y x ⊔ K x z) = Nat.card ↥(K x y ⊔ K y x)) : False := by
  have hcomm : Nat.card ↥(K y (f • y) ⊔ K (f • y) y) = Nat.card ↥(K x y ⊔ K y x) :=
    onanB_card_sup_comm h2 K hKconj hy'y.symm hxy
  have hcard : Nat.card ↥(K y x ⊔ P') = Nat.card ↥(K y x ⊔ K x z) := by
    calc Nat.card ↥(K y x ⊔ P')
        = Nat.card ↥(K y x ⊔ K (f • y) y) := by rw [hP'eq]
      _ = Nat.card ↥(K y (f • y) ⊔ K (f • y) y) := by rw [hPeq]
      _ = Nat.card ↥(K x y ⊔ K y x) := hcomm
      _ = Nat.card ↥(K y x ⊔ K x z) := hcardd.symm
  have hle : K y x ⊔ P' ≤ K y x ⊔ (K x z ⊓ Subgroup.normalizer (K y x : Set X)) :=
    sup_le le_sup_left hP'le
  have hlt : K y x ⊔ P' < K y x ⊔ K x z := lt_of_le_of_lt hle hsupRlt
  exact (ne_of_lt (Subgroup.card_lt_of_lt hlt)) hcard

private lemma onanB_witness_contradiction {X : Type} {Ω : Type*} [Group X] [Finite X]
    [MulAction X Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d)
    (K : Ω → Ω → Subgroup X)
    (hKfix : ∀ u v, u ≠ v → ∀ k ∈ K u v, k • u = u ∧ k • v = v)
    (hKconj : ∀ (g : X) (u v : Ω) (k : X), k ∈ K u v ↔ g * k * g⁻¹ ∈ K (g • u) (g • v))
    (hKsc : ∀ u v w, u ≠ v → u ≠ w → v ≠ w → ∀ k ∈ K u v, k • w = w → k ∈ K u w)
    {x y z : Ω} (hxy : x ≠ y) (hxz : x ≠ z)
    (hPnot : ¬ K y x ≤ K x y)
    (hPQ : K y x ≤ Subgroup.normalizer (K x z : Set X))
    (hcardd : Nat.card ↥(K y x ⊔ K x z) = Nat.card ↥(K x y ⊔ K y x))
    (hsupRlt : K y x ⊔ (K x z ⊓ Subgroup.normalizer (K y x : Set X)) < K y x ⊔ K x z)
    {f : X} (hfH : f ∈ K y x ⊔ K x z)
    (hfR : f ∉ K y x ⊔ (K x z ⊓ Subgroup.normalizer (K y x : Set X)))
    (hfconj : ∀ h ∈ K y x ⊔ (K x z ⊓ Subgroup.normalizer (K y x : Set X)),
      f * h * f⁻¹ ∈ K y x ⊔ (K x z ⊓ Subgroup.normalizer (K y x : Set X)))
    (hfconjInv : ∀ h ∈ K y x ⊔ (K x z ⊓ Subgroup.normalizer (K y x : Set X)),
      f⁻¹ * h * f ∈ K y x ⊔ (K x z ⊓ Subgroup.normalizer (K y x : Set X))) :
    False := by
  have hfx : f • x = x := onanB_sup_fixes_x K hKfix hxy hxz hfH
  have hfyy : f • y ≠ y := onanB_witness_moves_y K hKconj hKfix hxy hxz hPQ hfH hfR
  have hfyx : f • y ≠ x := by
    intro h
    have h1 : f • y = f • x := by rw [h, hfx]
    exact hxy (MulAction.injective f h1).symm
  have hNPle : Subgroup.normalizer (K y x : Set X) ≤ stabilizer X y :=
    onanB_normalizer_le_stabilizer h2 K hKfix hKconj hKsc hxy.symm hPnot
  set P' : Subgroup X := (K y x).map (MulAut.conj f).toMonoidHom with hP'def
  have hP'K : P' = K (f • y) x := by
    rw [hP'def]
    change (K y x).map (MulAut.conj f) = K (f • y) x
    rw [onanB_map_conj K hKconj f y x, hfx]
  have hP'le : P' ≤ K y x ⊔ (K x z ⊓ Subgroup.normalizer (K y x : Set X)) := by
    intro q hq
    rw [hP'def, Subgroup.mem_map] at hq
    obtain ⟨p0, hp0, rfl⟩ := hq
    simpa using hfconj p0 (Subgroup.mem_sup_left hp0)
  have hP'leN : P' ≤ Subgroup.normalizer (K y x : Set X) :=
    le_trans hP'le (sup_le Subgroup.le_normalizer inf_le_right)
  have hP'stab : P' ≤ stabilizer X y := le_trans hP'leN hNPle
  have hPleN' : K y x ≤ Subgroup.normalizer (P' : Set X) := by
    rw [hP'def]
    simpa using onanB_le_normalizer_map_conj hfconjInv inf_le_right
  have hN'le : Subgroup.normalizer (P' : Set X) ≤ stabilizer X (f • y) := by
    have hNmap : (Subgroup.normalizer (K y x : Set X)).map (MulAut.conj f).toMonoidHom =
        Subgroup.normalizer (P' : Set X) := by
      rw [hP'def]
      simpa using Subgroup.map_equiv_normalizer_eq (K y x) (MulAut.conj f)
    rw [← hNmap, MulAction.stabilizer_smul_eq_stabilizer_map_conj (G := X) f y]
    exact Subgroup.map_mono hNPle
  have hPfix : K y x ≤ stabilizer X (f • y) := le_trans hPleN' hN'le
  have hPeq : K y x = K y (f • y) :=
    onanB_eq_Kyy' h2 K hKconj hKsc hxy hfyy hfyx hPfix
  have hP'eq : P' = K (f • y) y := by
    rw [hP'def]
    exact onanB_eq_P' h2 K hKconj hKsc hxy hfyx hfyy hP'K hP'stab
  exact onanB_card_contradiction h2 K hKconj hxy hfyy hPeq hP'eq hP'le hsupRlt hcardd

private lemma onanB_inf_normalizer_eq {X : Type} {Ω : Type*} [Group X] [Finite X]
    [MulAction X Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d)
    {p : ℕ} [Fact p.Prime] (K : Ω → Ω → Subgroup X)
    (hKp : ∀ u v, u ≠ v → IsPGroup p (K u v))
    (hKfix : ∀ u v, u ≠ v → ∀ k ∈ K u v, k • u = u ∧ k • v = v)
    (hKconj : ∀ (g : X) (u v : Ω) (k : X), k ∈ K u v ↔ g * k * g⁻¹ ∈ K (g • u) (g • v))
    (hKsc : ∀ u v w, u ≠ v → u ≠ w → v ≠ w → ∀ k ∈ K u v, k • w = w → k ∈ K u w)
    {x y z : Ω} (hxy : x ≠ y) (hxz : x ≠ z) (hzy : z ≠ y)
    (hz : ∀ k ∈ K y x, k • z = z) (hPnot : ¬ K y x ≤ K x y) :
    K x z ⊓ Subgroup.normalizer (K y x : Set X) = K x z := by
  set Q := K x z with hQ
  set R := Q ⊓ Subgroup.normalizer (K y x : Set X) with hR
  have hRQ : R ≤ Q := inf_le_left
  by_contra hne
  have hRnorm : R ≤ Subgroup.normalizer (K y x : Set X) := inf_le_right
  have hsupRlt : K y x ⊔ R < K y x ⊔ Q := onanB_sup_lt_sup hRnorm hRQ hne hR
  have hPQ : K y x ≤ Subgroup.normalizer (Q : Set X) := fun k hk =>
    onanB_mem_normalizer_of_fixed K hKconj (hKfix y x hxy.symm k hk).2 (hz k hk)
  have hcardd : Nat.card ↥(K y x ⊔ Q) = Nat.card ↥(K x y ⊔ K y x) := by
    simpa [hQ] using onanB_card_sup_eq h2 K hKfix hKconj hKsc hxy hxz hzy hz
  obtain ⟨f, hfH, hfR, hfconj, hfconjInv⟩ :=
    onanB_exists_conj_witness (hKp y x hxy.symm) (by simpa [hQ] using hKp x z hxz) hPQ hsupRlt
  exact onanB_witness_contradiction h2 K hKfix hKconj hKsc hxy hxz hPnot hPQ hcardd
    hsupRlt hfH hfR hfconj hfconjInv

theorem fixed_of_fixed_of_isPGroup {X : Type} {Ω : Type*} [Group X] [Finite X] [MulAction X Ω]
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d)
    {p : ℕ} [Fact p.Prime] (K : Ω → Ω → Subgroup X)
    (hKp : ∀ u v, u ≠ v → IsPGroup p (K u v))
    (hKfix : ∀ u v, u ≠ v → ∀ k ∈ K u v, k • u = u ∧ k • v = v)
    (hKconj : ∀ (g : X) (u v : Ω) (k : X), k ∈ K u v ↔ g * k * g⁻¹ ∈ K (g • u) (g • v))
    (hKsc : ∀ u v w, u ≠ v → u ≠ w → v ≠ w → ∀ k ∈ K u v, k • w = w → k ∈ K u w)
    {x y z : Ω} (hxy : x ≠ y) (hz : ∀ k ∈ K y x, k • z = z) :
    ∀ k ∈ K x y, k • z = z := by
  by_cases hzx : z = x
  · subst z
    intro k hk
    exact (hKfix x y hxy k hk).1
  · by_cases hzy : z = y
    · subst z
      intro k hk
      exact (hKfix x y hxy k hk).2
    · by_cases hle : K y x ≤ K x y
      · have heq : K y x = K x y :=
          onanB_eq_of_le_natCard h2 K hKconj hxy.symm hxy hle
        intro k hk
        rw [← heq] at hk
        exact hz k hk
      · have hRQ : K x z ⊓ Subgroup.normalizer (K y x : Set X) = K x z :=
          onanB_inf_normalizer_eq h2 K hKp hKfix hKconj hKsc hxy (Ne.symm hzx) hzy hz hle
        have hNPle : Subgroup.normalizer (K y x : Set X) ≤ stabilizer X y :=
          onanB_normalizer_le_stabilizer h2 K hKfix hKconj hKsc hxy.symm hle
        have hQleN : K x z ≤ Subgroup.normalizer (K y x : Set X) := by
          rw [← hRQ]
          exact inf_le_right
        have hQstab : K x z ≤ stabilizer X y := le_trans hQleN hNPle
        have hQKxy : K x z ≤ K x y := fun k hk =>
          hKsc x z y (Ne.symm hzx) hxy hzy k hk
            (MulAction.mem_stabilizer_iff.mp (hQstab hk))
        have hQeq : K x z = K x y :=
          onanB_eq_of_le_natCard h2 K hKconj (Ne.symm hzx) hxy hQKxy
        intro k hk
        rw [← hQeq] at hk
        exact (hKfix x z (Ne.symm hzx) k hk).2

end CFSG.GroupTheory.ONan
