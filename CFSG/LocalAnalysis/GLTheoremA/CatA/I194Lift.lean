module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.LocalCores

variable {Y : Type} [Group Y]

@[expose] def conjJ (a : Y) (J : Subgroup Y) : Subgroup Y :=
  J.map (MulAut.conj a).toMonoidHom

theorem mem_conjJ {a x : Y} {J : Subgroup Y} : x ∈ conjJ a J ↔ a⁻¹ * x * a ∈ J := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [conjJ, MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨a⁻¹ * x * a, h, by simp [conjJ, MulAut.conj_apply, mul_assoc]⟩

theorem conjJ_mul (x y : Y) (J : Subgroup Y) : conjJ x (conjJ y J) = conjJ (x * y) J := by
  ext z
  rw [mem_conjJ, mem_conjJ, mem_conjJ, mul_inv_rev]
  constructor <;> intro h <;> simpa [mul_assoc] using h

theorem conjJ_one (J : Subgroup Y) : conjJ 1 J = J := by
  ext z
  rw [mem_conjJ]
  simp

theorem isComponent_conjJ {J : Subgroup Y} (hJ : IsComponent J) (a : Y) :
    IsComponent (conjJ a J) :=
  isComponent_map_mulEquiv (MulAut.conj a) hJ

theorem conjJ_eq_self_iff {J : Subgroup Y} {a : Y} :
    conjJ a J = J ↔ a ∈ Subgroup.normalizer (J : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    have hx : ∀ z, z ∈ conjJ a J ↔ z ∈ J := fun z => by rw [h]
    have := hx (a * x * a⁻¹)
    rw [mem_conjJ] at this
    have e : a⁻¹ * (a * x * a⁻¹) * a = x := by group
    rw [e] at this
    exact this
  · intro h
    ext z
    rw [mem_conjJ]
    have := h (a⁻¹ * z * a)
    have e : a * (a⁻¹ * z * a) * a⁻¹ = z := by group
    rw [e] at this
    exact this

theorem conjJ_eq_conjJ_iff {J : Subgroup Y} {a b : Y} :
    conjJ a J = conjJ b J ↔ b⁻¹ * a ∈ Subgroup.normalizer (J : Set Y) := by
  rw [← conjJ_eq_self_iff]
  constructor
  · intro h
    have h1 := congrArg (conjJ b⁻¹) h
    rw [conjJ_mul, conjJ_mul, inv_mul_cancel, conjJ_one] at h1
    exact h1
  · intro h
    have h2 : conjJ (b⁻¹ * a) J = J := h
    calc conjJ a J = conjJ (b * (b⁻¹ * a)) J := by rw [mul_inv_cancel_left]
      _ = conjJ b (conjJ (b⁻¹ * a) J) := (conjJ_mul _ _ _).symm
      _ = conjJ b J := by rw [h2]

@[expose] def orbitLayer (A J : Subgroup Y) : Subgroup Y :=
  ⨆ a : A, conjJ (a : Y) J

theorem le_orbitLayer {A J : Subgroup Y} (a : A) : conjJ (a : Y) J ≤ orbitLayer A J :=
  le_iSup (fun a : A => conjJ (a : Y) J) a

theorem commute_of_comp_ne [Finite Y] {K L : Subgroup Y} (hK : IsComponent K)
    (hL : IsComponent L) (hne : K ≠ L) {x y : Y} (hx : x ∈ K) (hy : y ∈ L) : x * y = y * x := by
  rcases distinct_components_commute hK hL with h | h
  · exact absurd h hne
  · exact ((Subgroup.mem_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h hx))
      y hy).symm

theorem exists_transversal [Finite Y] (A H : Subgroup Y)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hH : H ≤ A) :
    ∃ T : List Y, T.Nodup ∧ (∀ t ∈ T, t ∈ A) ∧
      (∀ t ∈ T, ∀ s ∈ T, t⁻¹ * s ∈ H → t = s) ∧ (∀ x ∈ A, ∃ t ∈ T, t⁻¹ * x ∈ H) := by
  classical
  have hnorm : (H.subgroupOf A).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc : (g : Y) * (n : Y) * (g : Y)⁻¹ = (n : Y) := by
      rw [hA g g.2 n n.2, mul_inv_cancel_right]
    show (g : Y) * (n : Y) * (g : Y)⁻¹ ∈ H
    rw [hc]
    exact hn
  letI : Fintype (↥A ⧸ H.subgroupOf A) := Fintype.ofFinite _
  refine ⟨(Finset.univ.image fun q : ↥A ⧸ H.subgroupOf A =>
      ((Quotient.out q : ↥A) : Y)).toList, Finset.nodup_toList _, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_toList.1 ht)
    exact (Quotient.out q : ↥A).2
  · intro t ht s hs hts
    obtain ⟨q1, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_toList.1 ht)
    obtain ⟨q2, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_toList.1 hs)
    have hmk : (QuotientGroup.mk (Quotient.out q1 : ↥A) : ↥A ⧸ H.subgroupOf A) =
        QuotientGroup.mk (Quotient.out q2 : ↥A) := by
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using hts
    have hq : q1 = q2 := by
      calc q1 = QuotientGroup.mk (Quotient.out q1 : ↥A) := (Quotient.out_eq' q1).symm
        _ = QuotientGroup.mk (Quotient.out q2 : ↥A) := hmk
        _ = q2 := Quotient.out_eq' q2
    rw [hq]
  · intro x hx
    obtain ⟨q, hq⟩ : ∃ q : ↥A ⧸ H.subgroupOf A, q = QuotientGroup.mk (⟨x, hx⟩ : ↥A) := ⟨_, rfl⟩
    refine ⟨((Quotient.out q : ↥A) : Y), ?_, ?_⟩
    · rw [Finset.mem_toList]
      exact Finset.mem_image.2 ⟨q, Finset.mem_univ _, rfl⟩
    · have h1 : (QuotientGroup.mk (Quotient.out q : ↥A) : ↥A ⧸ H.subgroupOf A) = q :=
        Quotient.out_eq' q
      have h2 := QuotientGroup.eq.1 (h1.trans hq)
      rw [Subgroup.mem_subgroupOf] at h2
      simpa using h2

theorem conj_mem_of_mem_normalizer {J : Subgroup Y} {x : Y} (hx : x ∈ Subgroup.normalizer (J : Set Y))
    {y : Y} (hy : y ∈ J) : x * y * x⁻¹ ∈ J :=
  (Subgroup.mem_normalizer_iff.1 hx y).1 hy

theorem list_prod_central_mul {L : Subgroup Y} {α : Type*} (l : List α) (c g' : α → Y)
    (hc : ∀ t ∈ l, c t ∈ Subgroup.centralizer (L : Set Y)) (hg' : ∀ t ∈ l, g' t ∈ L) :
    (l.map fun t => c t * g' t).prod = (l.map c).prod * (l.map g').prod := by
  induction l with
  | nil => simp
  | cons t l ih =>
    have ih' := ih (fun s hs => hc s (List.mem_cons_of_mem _ hs))
      (fun s hs => hg' s (List.mem_cons_of_mem _ hs))
    have hC : (l.map c).prod ∈ Subgroup.centralizer (L : Set Y) :=
      Subgroup.list_prod_mem _ (fun z hz => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hz
        exact hc s (List.mem_cons_of_mem _ hs))
    have hgC : g' t * (l.map c).prod = (l.map c).prod * g' t :=
      (Subgroup.mem_centralizer_iff.1 hC) (g' t) (hg' t (List.mem_cons_self))
    rw [List.map_cons, List.prod_cons, ih', List.map_cons, List.prod_cons]
    calc c t * g' t * ((l.map c).prod * (l.map g').prod)
        = c t * (g' t * (l.map c).prod) * (l.map g').prod := by group
      _ = c t * ((l.map c).prod * g' t) * (l.map g').prod := by rw [hgC]
      _ = c t * (l.map c).prod * (g' t * (l.map g').prod) := by group

theorem list_prod_perm_map {α : Type*} (l : List α) (σ : α → α) (f : α → Y)
    (hperm : List.Perm (l.map σ) l) (hcomm : (l.map f).Pairwise Commute) :
    ((l.map σ).map f).prod = (l.map f).prod := by
  have hp : List.Perm ((l.map σ).map f) (l.map f) := hperm.map f
  have hc : ((l.map σ).map f).Pairwise Commute :=
    hcomm.perm hp.symm (fun h => h.symm)
  exact hp.prod_eq' hc

theorem mem_centralizer_orbitLayer {A J : Subgroup Y} {c : Y}
    (hc : ∀ s ∈ A, ∀ v ∈ conjJ s J, c * v = v * c) :
    c ∈ Subgroup.centralizer (orbitLayer A J : Set Y) := by
  have hle : orbitLayer A J ≤ Subgroup.centralizer ({c} : Set Y) := by
    refine iSup_le fun s => ?_
    intro v hv
    exact Subgroup.mem_centralizer_singleton_iff.2 (hc s.1 s.2 v hv).symm
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)

theorem z_mem {J : Subgroup Y} {j b : Y} (hj : j ∈ J) (hbN : b ∈ Subgroup.normalizer (J : Set Y)) :
    b * j * b⁻¹ * j⁻¹ ∈ J :=
  J.mul_mem (conj_mem_of_mem_normalizer hbN hj) (J.inv_mem hj)

theorem z_centralizes {A J : Subgroup Y} {j : Y} (hj : j ∈ J)
    (hcomm : ∀ a ∈ A, a ∈ Subgroup.normalizer (J : Set Y) → ∀ y ∈ J,
      a * (j * y * j⁻¹) * a⁻¹ = j * (a * y * a⁻¹) * j⁻¹)
    {b : Y} (hbA : b ∈ A) (hbN : b ∈ Subgroup.normalizer (J : Set Y)) :
    ∀ w ∈ J, (b * j * b⁻¹ * j⁻¹) * w * (b * j * b⁻¹ * j⁻¹)⁻¹ = w := by
  intro w hw
  have hjw : j⁻¹ * w * j ∈ J := J.mul_mem (J.mul_mem (J.inv_mem hj) hw) hj
  have hyJ : b⁻¹ * (j⁻¹ * w * j) * b ∈ J := by
    have := conj_mem_of_mem_normalizer (Subgroup.inv_mem _ hbN) hjw
    simpa using this
  have key := hcomm b hbA hbN _ hyJ
  have e1 : b * (j * (b⁻¹ * (j⁻¹ * w * j) * b) * j⁻¹) * b⁻¹ =
      (b * j * b⁻¹ * j⁻¹) * w * (b * j * b⁻¹ * j⁻¹)⁻¹ := by group
  have e2 : j * (b * (b⁻¹ * (j⁻¹ * w * j) * b) * b⁻¹) * j⁻¹ = w := by group
  rw [e1, e2] at key
  exact key

theorem central_conj_mem [Finite Y] {A J : Subgroup Y} (hJ : IsComponent J) {j : Y} (hj : j ∈ J)
    (hcomm : ∀ a ∈ A, a ∈ Subgroup.normalizer (J : Set Y) → ∀ y ∈ J,
      a * (j * y * j⁻¹) * a⁻¹ = j * (a * y * a⁻¹) * j⁻¹)
    {b : Y} (hbA : b ∈ A) (hbN : b ∈ Subgroup.normalizer (J : Set Y)) (u : Y) :
    u * (b * j * b⁻¹ * j⁻¹) * u⁻¹ ∈ Subgroup.centralizer (orbitLayer A J : Set Y) := by
  have hzJ := z_mem hj hbN
  have hzc := z_centralizes hj hcomm hbA hbN
  set z := b * j * b⁻¹ * j⁻¹ with hz
  apply mem_centralizer_orbitLayer
  intro s _ v hv
  by_cases hsu : conjJ s J = conjJ u J
  · have hv' : v ∈ conjJ u J := hsu ▸ hv
    have hw : u⁻¹ * v * u ∈ J := mem_conjJ.1 hv'
    have h0 := hzc _ hw
    have hzw : z * (u⁻¹ * v * u) = (u⁻¹ * v * u) * z := by
      calc z * (u⁻¹ * v * u) = (z * (u⁻¹ * v * u) * z⁻¹) * z := by group
        _ = (u⁻¹ * v * u) * z := by rw [h0]
    calc u * z * u⁻¹ * v = u * (z * (u⁻¹ * v * u)) * u⁻¹ := by group
      _ = u * ((u⁻¹ * v * u) * z) * u⁻¹ := by rw [hzw]
      _ = v * (u * z * u⁻¹) := by group
  · have hcJ : u * z * u⁻¹ ∈ conjJ u J := by
      apply mem_conjJ.2
      have e : u⁻¹ * (u * z * u⁻¹) * u = z := by group
      rw [e]
      exact hzJ
    exact commute_of_comp_ne (isComponent_conjJ hJ u) (isComponent_conjJ hJ s)
      (fun h => hsu h.symm) hcJ hv

theorem exists_orbit_lift [Finite Y] {A J : Subgroup Y} (hJ : IsComponent J)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {j : Y} (hj : j ∈ J)
    (hcomm : ∀ a ∈ A, a ∈ Subgroup.normalizer (J : Set Y) → ∀ y ∈ J,
      a * (j * y * j⁻¹) * a⁻¹ = j * (a * y * a⁻¹) * j⁻¹) :
    ∃ x : Y, x ∈ orbitLayer A J ∧ x ∈ Subgroup.normalizer (J : Set Y) ∧
      (∀ y ∈ J, x * y * x⁻¹ = j * y * j⁻¹) ∧
      ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ Subgroup.centralizer (orbitLayer A J : Set Y) := by
  classical
  set AJ : Subgroup Y := A ⊓ Subgroup.normalizer (J : Set Y) with hAJ
  obtain ⟨T, hTnd, hTA, hTu, hTe⟩ := exists_transversal A AJ hA inf_le_left
  choose! sel hselT hselH using hTe
  have hselu : ∀ x ∈ A, ∀ t ∈ T, t⁻¹ * x ∈ AJ → t = sel x := by
    intro x hx t ht h
    apply hTu t ht (sel x) (hselT x hx)
    have e : t⁻¹ * sel x = (t⁻¹ * x) * ((sel x)⁻¹ * x)⁻¹ := by group
    rw [e]
    exact AJ.mul_mem h (AJ.inv_mem (hselH x hx))
  obtain ⟨g, hg⟩ : ∃ g : Y → Y, ∀ t, g t = t * j * t⁻¹ := ⟨fun t => t * j * t⁻¹, fun t => rfl⟩
  have hg_mem : ∀ t, g t ∈ conjJ t J := fun t => by
    rw [hg]
    exact ⟨j, hj, rfl⟩
  have hg_orb : ∀ t ∈ T, g t ∈ orbitLayer A J := fun t ht =>
    le_orbitLayer (⟨t, hTA t ht⟩ : A) (hg_mem t)
  have hne : ∀ t ∈ T, ∀ s ∈ T, t ≠ s → conjJ t J ≠ conjJ s J := by
    intro t ht s hs hts heq
    apply hts
    apply hTu t ht s hs
    have h1 : s⁻¹ * t ∈ Subgroup.normalizer (J : Set Y) := conjJ_eq_conjJ_iff.1 heq
    rw [hAJ, Subgroup.mem_inf]
    refine ⟨A.mul_mem (A.inv_mem (hTA t ht)) (hTA s hs), ?_⟩
    have := (Subgroup.normalizer (J : Set Y)).inv_mem h1
    simpa [mul_inv_rev] using this
  have hperm : ∀ a ∈ A, List.Perm (T.map fun t => sel (a * t)) T := by
    intro a ha
    have hTA' : ∀ t ∈ T, a * t ∈ A := fun t ht => A.mul_mem ha (hTA t ht)
    have hinj : ∀ t ∈ T, ∀ s ∈ T, sel (a * t) = sel (a * s) → t = s := by
      intro t ht s hs hts
      apply hTu t ht s hs
      have h1 := hselH (a * t) (hTA' t ht)
      have h2 := hselH (a * s) (hTA' s hs)
      rw [hts] at h1
      have e : t⁻¹ * s = ((sel (a * s))⁻¹ * (a * t))⁻¹ * ((sel (a * s))⁻¹ * (a * s)) := by group
      rw [e]
      exact AJ.mul_mem (AJ.inv_mem h1) h2
    refine (List.perm_ext_iff_of_nodup ?_ hTnd).2 ?_
    · exact List.Nodup.map_on (fun t ht s hs hts => hinj t ht s hs hts) hTnd
    · intro x
      constructor
      · intro hx
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
        exact hselT (a * t) (hTA' t ht)
      · intro hx
        have ha' : a⁻¹ * x ∈ A := A.mul_mem (A.inv_mem ha) (hTA x hx)
        have hth := hselH (a⁻¹ * x) ha'
        have ht := hselT (a⁻¹ * x) ha'
        refine List.mem_map.2 ⟨sel (a⁻¹ * x), ht, ?_⟩
        have hmem : x⁻¹ * (a * sel (a⁻¹ * x)) ∈ AJ := by
          have e : x⁻¹ * (a * sel (a⁻¹ * x)) = ((sel (a⁻¹ * x))⁻¹ * (a⁻¹ * x))⁻¹ := by group
          rw [e]
          exact AJ.inv_mem hth
        exact (hselu (a * sel (a⁻¹ * x)) (hTA' _ ht) x hx hmem).symm
  obtain ⟨t0, ht0T, ht0⟩ : ∃ t0, t0 ∈ T ∧ t0⁻¹ * 1 ∈ AJ :=
    ⟨sel 1, hselT 1 A.one_mem, hselH 1 A.one_mem⟩
  have ht0AJ : t0 ∈ AJ := by
    have h : t0⁻¹ ∈ AJ := by simpa using ht0
    simpa using AJ.inv_mem h
  have ht0A : t0 ∈ A := (Subgroup.mem_inf.1 ht0AJ).1
  have ht0N : t0 ∈ Subgroup.normalizer (J : Set Y) := (Subgroup.mem_inf.1 ht0AJ).2
  have hXpair : ((T.map g)).Pairwise Commute := by
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem (fun {t s} ht hs hts => ?_) hTnd
    exact commute_of_comp_ne (isComponent_conjJ hJ t) (isComponent_conjJ hJ s)
      (hne t ht s hs hts) (hg_mem t) (hg_mem s)
  have hXsplit : (T.map g).prod = g t0 * ((T.erase t0).map g).prod := by
    rw [((List.perm_cons_erase ht0T).map g).prod_eq' hXpair]
    simp only [List.map_cons, List.prod_cons]
  have hR_comm : ∀ y ∈ J, ((T.erase t0).map g).prod * y = y * ((T.erase t0).map g).prod := by
    intro y hy
    have hc : Commute ((T.erase t0).map g).prod y := by
      apply Commute.list_prod_left
      intro b hb
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hb
      have hsT : s ∈ T := List.mem_of_mem_erase hs
      have hst : s ≠ t0 := ((List.Nodup.mem_erase_iff hTnd).1 hs).1
      have hsJ : conjJ s J ≠ J := by
        intro heq
        have hsN : s ∈ Subgroup.normalizer (J : Set Y) := conjJ_eq_self_iff.1 heq
        have hmem : t0⁻¹ * s ∈ AJ := by
          rw [hAJ, Subgroup.mem_inf]
          refine ⟨A.mul_mem (A.inv_mem ht0A) (hTA s hsT), ?_⟩
          exact (Subgroup.normalizer (J : Set Y)).mul_mem (Subgroup.inv_mem _ ht0N) hsN
        exact hst (hTu t0 ht0T s hsT hmem).symm
      exact commute_of_comp_ne (isComponent_conjJ hJ s) hJ hsJ (hg_mem s) hy
    exact hc
  have hu : ∀ y ∈ J, (t0 * j * t0⁻¹) * y * (t0 * j * t0⁻¹)⁻¹ = j * y * j⁻¹ := by
    intro y hy
    have hy' : t0⁻¹ * y * t0 ∈ J := by
      have := conj_mem_of_mem_normalizer (Subgroup.inv_mem _ ht0N) hy
      simpa using this
    have h := hcomm t0 ht0A ht0N (t0⁻¹ * y * t0) hy'
    have e : t0 * (t0⁻¹ * y * t0) * t0⁻¹ = y := by group
    rw [e] at h
    calc (t0 * j * t0⁻¹) * y * (t0 * j * t0⁻¹)⁻¹ = t0 * (j * (t0⁻¹ * y * t0) * j⁻¹) * t0⁻¹ := by
          group
      _ = j * y * j⁻¹ := h
  have hXy : ∀ y ∈ J, (T.map g).prod * y * ((T.map g).prod)⁻¹ = j * y * j⁻¹ := by
    intro y hy
    rw [hXsplit]
    calc (g t0 * ((T.erase t0).map g).prod) * y * (g t0 * ((T.erase t0).map g).prod)⁻¹
        = g t0 * (((T.erase t0).map g).prod * y) * ((T.erase t0).map g).prod⁻¹ * (g t0)⁻¹ := by
          group
      _ = g t0 * (y * ((T.erase t0).map g).prod) * ((T.erase t0).map g).prod⁻¹ * (g t0)⁻¹ := by
          rw [hR_comm y hy]
      _ = g t0 * y * (g t0)⁻¹ := by group
      _ = j * y * j⁻¹ := by rw [hg t0]; exact hu y hy
  have hRN : ((T.erase t0).map g).prod ∈ Subgroup.normalizer (J : Set Y) := by
    set R := ((T.erase t0).map g).prod with hRdef
    have hfix : ∀ y ∈ J, R * y * R⁻¹ = y := fun y hy => by
      rw [hR_comm y hy]
      group
    have hfix' : ∀ y ∈ J, R⁻¹ * y * R = y := fun y hy => by
      calc R⁻¹ * y * R = R⁻¹ * (R * y * R⁻¹) * R := by rw [hfix y hy]
        _ = y := by group
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hfix h hh]
      exact hh
    · intro hh
      have h3 : R⁻¹ * (R * h * R⁻¹) * R ∈ J := by
        rw [hfix' _ hh]
        exact hh
      have e : R⁻¹ * (R * h * R⁻¹) * R = h := by group
      rw [e] at h3
      exact h3
  refine ⟨(T.map g).prod, ?_, ?_, fun y hy => hXy y hy, ?_⟩
  · refine Subgroup.list_prod_mem _ (fun z hz => ?_)
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hz
    exact hg_orb t ht
  · rw [hXsplit]
    refine (Subgroup.normalizer (J : Set Y)).mul_mem ?_ hRN
    apply Subgroup.le_normalizer
    rw [hg t0]
    exact conj_mem_of_mem_normalizer ht0N hj
  intro a ha
  have hA' : ∀ t ∈ T, a * t ∈ A := fun t ht => A.mul_mem ha (hTA t ht)
  obtain ⟨cc, hcc⟩ : ∃ cc : Y → Y, ∀ t, cc t = sel (a * t) * ((sel (a * t))⁻¹ * (a * t) * j *
      ((sel (a * t))⁻¹ * (a * t))⁻¹ * j⁻¹) * (sel (a * t))⁻¹ := ⟨_, fun t => rfl⟩
  have hF1 : ∀ t ∈ T, a * g t * a⁻¹ = cc t * g (sel (a * t)) := by
    intro t _
    rw [hcc t, hg t, hg (sel (a * t))]
    group
  have hF2 : ∀ t ∈ T, cc t ∈ Subgroup.centralizer (orbitLayer A J : Set Y) := by
    intro t ht
    have hbAJ : (sel (a * t))⁻¹ * (a * t) ∈ AJ := hselH _ (hA' t ht)
    rw [hcc t]
    exact central_conj_mem hJ hj hcomm (Subgroup.mem_inf.1 hbAJ).1 (Subgroup.mem_inf.1 hbAJ).2
      (sel (a * t))
  have hg' : ∀ t ∈ T, g (sel (a * t)) ∈ orbitLayer A J := fun t ht =>
    hg_orb _ (hselT _ (hA' t ht))
  have hconj : a * (T.map g).prod * a⁻¹ = (T.map fun t => a * g t * a⁻¹).prod := by
    have h := map_list_prod (MulAut.conj a) (T.map g)
    simpa [MulAut.conj_apply, List.map_map, Function.comp_def] using h
  have hstep : (T.map fun t => a * g t * a⁻¹) = T.map fun t => cc t * g (sel (a * t)) :=
    List.map_congr_left (fun t ht => hF1 t ht)
  have hcprod := list_prod_central_mul (L := orbitLayer A J) T cc (fun t => g (sel (a * t)))
    hF2 hg'
  have hperm_prod := list_prod_perm_map T (fun t => sel (a * t)) g (hperm a ha) hXpair
  rw [List.map_map] at hperm_prod
  have hfin : a * (T.map g).prod * a⁻¹ = (T.map cc).prod * (T.map g).prod := by
    rw [hconj, hstep, hcprod]
    congr 1
  have hc' : a * (T.map g).prod * a⁻¹ * ((T.map g).prod)⁻¹ = (T.map cc).prod := by
    rw [hfin]
    group
  rw [hc']
  refine Subgroup.list_prod_mem _ (fun z hz => ?_)
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hz
  exact hF2 t ht

end CFSG.LocalAnalysis.GLTheoremA
