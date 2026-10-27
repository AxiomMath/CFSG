module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S16AGrp
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5CompFix
public import CFSG.Holt.TwoGroups

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.S16A

open Subgroup CFSG.Open

section PLevel

variable {P : Type*} [Group P] [Finite P]

structure PHyp (S V : Subgroup P) (t : P) : Prop where
  isPGroup : IsPGroup 2 P
  index_two : S.index = 2
  t_notMem : t ∉ S
  t_sq : t * t = 1
  V_elem : IsElemAbelian 2 V
  V_le : V ≤ S
  V_central : ∀ v ∈ V, ∀ s ∈ S, v * s = s * v
  t_normV : ∀ v ∈ V, t * v * t⁻¹ ∈ V
  V_trans : ∀ w ∈ V, t * w * t⁻¹ = w → ∃ v ∈ V, w = v * (t * v⁻¹ * t⁻¹)
  card_le : Nat.card ↥(S ⊓ centralizer ({t} : Set P)) ≤
    2 * Nat.card ↥(V ⊓ centralizer ({t} : Set P))

variable {S V : Subgroup P} {t : P}

theorem PHyp.t_inv (h : PHyp S V t) : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq

theorem PHyp.exists_mul_t (h : PHyp S V t) {y : P} (hy : y ∉ S) : ∃ s ∈ S, y = s * t := by
  refine ⟨y * t, ?_, by rw [mul_assoc, h.t_sq, mul_one]⟩
  rw [Subgroup.mul_mem_iff_of_index_two h.index_two]
  exact iff_of_false hy h.t_notMem

theorem PHyp.act_eq (h : PHyp S V t) {y : P} (hy : y ∉ S) {v : P} (hv : v ∈ V) :
    y * v * y⁻¹ = t * v * t⁻¹ := by
  obtain ⟨s, hs, rfl⟩ := h.exists_mul_t hy
  have hcomm : s * (t * v * t⁻¹) = (t * v * t⁻¹) * s :=
    (h.V_central _ (h.t_normV v hv) s hs).symm
  calc s * t * v * (s * t)⁻¹ = s * (t * v * t⁻¹) * s⁻¹ := by group
    _ = t * v * t⁻¹ := by rw [hcomm]; group

theorem PHyp.V_normal (h : PHyp S V t) : V.Normal := by
  refine ⟨fun v hv g => ?_⟩
  by_cases hg : g ∈ S
  · rw [← h.V_central v hv g hg]
    simpa using hv
  · rw [h.act_eq hg hv]
    exact h.t_normV v hv

theorem PHyp.exists_conj_of_mem_coset (h : PHyp S V t) {y x : P} (hy : y ∉ S) (hy2 : y * y = 1)
    (hx2 : x * x = 1) (hxy : y⁻¹ * x ∈ V) : ∃ w ∈ V, x = w * y * w⁻¹ := by
  set v := y⁻¹ * x with hv
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hxv : x = y * v := by rw [hv, hyi, ← mul_assoc, hy2, one_mul]
  have hV2 : ∀ u ∈ V, u * u = 1 := fun u hu => by
    have := h.V_elem.2 u hu
    rwa [pow_two] at this
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.V_elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hV2 v hxy)
  have htv : t * v * t⁻¹ = v := by
    have h1 : y * v * y⁻¹ = t * v * t⁻¹ := h.act_eq hy hxy
    have h2 : x * x = (y * v * y⁻¹) * v := by
      rw [hxv]
      calc y * v * (y * v) = y * v * y⁻¹ * (y * y) * v := by group
        _ = (y * v * y⁻¹) * v := by rw [hy2]; group
    rw [hx2, h1] at h2
    have h3 : t * v * t⁻¹ = v⁻¹ := by
      have := congrArg (· * v⁻¹) h2.symm
      simpa using this
    rw [h3, hvinv]
  obtain ⟨u, hu, hvu⟩ := h.V_trans v hxy htv
  refine ⟨u⁻¹, Subgroup.inv_mem _ hu, ?_⟩
  have hu' : t * u⁻¹ * t⁻¹ ∈ V := h.t_normV _ (Subgroup.inv_mem V hu)
  have h5 : y * u⁻¹ * y⁻¹ = t * u⁻¹ * t⁻¹ := h.act_eq hy (Subgroup.inv_mem V hu)
  have h7 : u * (t * u⁻¹ * t⁻¹) = (t * u⁻¹ * t⁻¹) * u := hcomm _ hu _ hu'
  calc x = y * v := hxv
    _ = y * ((t * u⁻¹ * t⁻¹) * u) := by rw [hvu, h7]
    _ = u⁻¹ * y * u⁻¹⁻¹ := by
      rw [← h5, inv_inv]
      calc y * (y * u⁻¹ * y⁻¹ * u) = (y * y) * u⁻¹ * y⁻¹ * u := by group
        _ = u⁻¹ * y⁻¹ * u := by rw [hy2, one_mul]
        _ = u⁻¹ * y * u := by rw [hyi]

theorem PHyp.exists_centralizer_of_comm_mod (h : PHyp S V t) {s : P} (hs : s ∈ S)
    (hcomm : (t * s)⁻¹ * (s * t) ∈ V) : ∃ c ∈ S, c * t = t * c ∧ s⁻¹ * c ∈ V := by
  have hti := h.t_inv
  have h1 : t⁻¹ * (s⁻¹ * t * s) ∈ V := by
    have := h.t_normV _ hcomm
    have e : t * ((t * s)⁻¹ * (s * t)) * t⁻¹ = t⁻¹ * (s⁻¹ * t * s) := by
      rw [mul_inv_rev, hti]
      calc t * (s⁻¹ * t * (s * t)) * t = (t * s⁻¹ * t * s) * (t * t) := by group
        _ = t * (s⁻¹ * t * s) := by rw [h.t_sq]; group
    rwa [e] at this
  have hx2 : (s⁻¹ * t * s) * (s⁻¹ * t * s) = 1 := by
    calc (s⁻¹ * t * s) * (s⁻¹ * t * s) = s⁻¹ * (t * t) * s := by group
      _ = 1 := by rw [h.t_sq]; group
  obtain ⟨w, hw, hws⟩ := h.exists_conj_of_mem_coset h.t_notMem h.t_sq hx2 h1
  refine ⟨s * w, Subgroup.mul_mem _ hs (h.V_le hw), ?_, ?_⟩
  · calc s * w * t = s * (w * t * w⁻¹) * w := by group
      _ = s * (s⁻¹ * t * s) * w := by rw [← hws]
      _ = t * (s * w) := by group
  · simpa using hw

theorem card_eq_mul [V.Normal] (h : PHyp S V t) :
    Nat.card ↥(S ⊓ centralizer ({t} : Set P)) =
      Nat.card ↥(V ⊓ centralizer ({t} : Set P)) *
        Nat.card ↥(S.map (QuotientGroup.mk' V) ⊓
          centralizer ({QuotientGroup.mk' V t} : Set (P ⧸ V))) := by
  set C := S ⊓ centralizer ({t} : Set P) with hC
  let ψ : ↥C →* P ⧸ V := (QuotientGroup.mk' V).comp C.subtype
  have hker : ψ.ker = (V ⊓ centralizer ({t} : Set P)).subgroupOf C := by
    ext c
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hc
      exact ⟨(QuotientGroup.eq_one_iff _).1 hc, (Subgroup.mem_inf.1 c.2).2⟩
    · rintro ⟨hv, -⟩
      exact (QuotientGroup.eq_one_iff _).2 hv
  have hrange : ψ.range =
      S.map (QuotientGroup.mk' V) ⊓ centralizer ({QuotientGroup.mk' V t} : Set (P ⧸ V)) := by
    ext q
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨hcS, hcC⟩ := Subgroup.mem_inf.1 c.2
      refine Subgroup.mem_inf.2 ⟨⟨c, hcS, rfl⟩, ?_⟩
      have hcC' : (c : P) * t = t * (c : P) := Subgroup.mem_centralizer_singleton_iff.1 hcC
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      show QuotientGroup.mk' V (c : P) * QuotientGroup.mk' V t =
        QuotientGroup.mk' V t * QuotientGroup.mk' V (c : P)
      rw [← map_mul, ← map_mul, hcC']
    · rintro ⟨⟨s, hs, rfl⟩, hq⟩
      have hq0 : QuotientGroup.mk' V s * QuotientGroup.mk' V t =
          QuotientGroup.mk' V t * QuotientGroup.mk' V s := Subgroup.mem_centralizer_singleton_iff.1 hq
      have hq' : (QuotientGroup.mk' V) (t * s) = (QuotientGroup.mk' V) (s * t) := by
        rw [map_mul, map_mul]; exact hq0.symm
      have hv : (t * s)⁻¹ * (s * t) ∈ V := (QuotientGroup.eq).1 hq'
      obtain ⟨c, hcS, hct, hsc⟩ := h.exists_centralizer_of_comm_mod hs hv
      have hcC : c ∈ C := Subgroup.mem_inf.2 ⟨hcS, Subgroup.mem_centralizer_singleton_iff.2 hct⟩
      refine ⟨⟨c, hcC⟩, ?_⟩
      show QuotientGroup.mk' V c = QuotientGroup.mk' V s
      exact ((QuotientGroup.eq).2 hsc).symm
  have hcard := Subgroup.card_ker_mul_card_range ψ
  rw [hker, hrange] at hcard
  have hle : V ⊓ centralizer ({t} : Set P) ≤ C := inf_le_inf_right _ h.V_le
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hcard
  exact hcard.symm

theorem card_quot_le [V.Normal] (h : PHyp S V t) :
    Nat.card ↥(S.map (QuotientGroup.mk' V) ⊓
      centralizer ({QuotientGroup.mk' V t} : Set (P ⧸ V))) ≤ 2 := by
  have h1 := card_eq_mul h
  have hpos : 0 < Nat.card ↥(V ⊓ centralizer ({t} : Set P)) := Nat.card_pos
  have h2 := h.card_le
  rw [h1] at h2
  rw [mul_comm 2] at h2
  exact Nat.le_of_mul_le_mul_left h2 hpos

theorem PHyp.conj_mem_map (h : PHyp S V t) {q : P ⧸ V} [V.Normal]
    (hq : q ∈ S.map (QuotientGroup.mk' V)) :
    QuotientGroup.mk' V t * q * (QuotientGroup.mk' V t)⁻¹ ∈ S.map (QuotientGroup.mk' V) := by
  obtain ⟨s, hs, rfl⟩ := hq
  have hN : S.Normal := Subgroup.normal_of_index_eq_two h.index_two
  refine ⟨t * s * t⁻¹, hN.conj_mem s hs t, ?_⟩
  simp [map_mul, map_inv]

theorem card_quot_ge [V.Normal] (h : PHyp S V t) (hne : S ≠ V) :
    2 ≤ Nat.card ↥(S.map (QuotientGroup.mk' V) ⊓
      centralizer ({QuotientGroup.mk' V t} : Set (P ⧸ V))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 (P ⧸ V) := h.isPGroup.to_quotient V
  set St := S.map (QuotientGroup.mk' V) with hSt
  have hne1 : St ≠ ⊥ := by
    intro hbot
    apply hne
    apply le_antisymm _ h.V_le
    intro s hs
    have : QuotientGroup.mk' V s ∈ St := ⟨s, hs, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff s).1 this
  have hdvd : 2 ∣ Nat.card St := by
    have hSt2 : IsPGroup 2 St := hQ.to_subgroup St
    rcases hSt2.card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.1 h1) hne1
    · exact h1
  have hcomm2 : (MulAut.conj (QuotientGroup.mk' V t)) ^ 2 = 1 := by
    rw [← map_pow]
    have : (QuotientGroup.mk' V t) ^ 2 = 1 := by
      rw [sq, ← map_mul, h.t_sq, map_one]
    rw [this, map_one]
  obtain ⟨b, hbS, hb1, hbfix⟩ := N.P5.Comp.exists_fixed_ne_one hcomm2
    (B := St) (fun b hb => by
      rw [MulAut.conj_apply]
      exact h.conj_mem_map hb) hdvd
  have hbC : b ∈ centralizer ({QuotientGroup.mk' V t} : Set (P ⧸ V)) := by
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have := hbfix
    simp only [MulAut.conj_apply] at this
    calc b * QuotientGroup.mk' V t = (QuotientGroup.mk' V t * b * (QuotientGroup.mk' V t)⁻¹) *
        QuotientGroup.mk' V t := by rw [this]
      _ = QuotientGroup.mk' V t * b := by group
  have hnt : Nontrivial ↥(St ⊓ centralizer ({QuotientGroup.mk' V t} : Set (P ⧸ V))) :=
    ⟨⟨1, one_mem _⟩, ⟨b, Subgroup.mem_inf.2 ⟨hbS, hbC⟩⟩, fun heq => hb1 (congrArg Subtype.val heq).symm⟩
  exact Finite.one_lt_card_iff_nontrivial.2 hnt

theorem card_quot_eq [V.Normal] (h : PHyp S V t) (hne : S ≠ V) :
    Nat.card ↥(S.map (QuotientGroup.mk' V) ⊓
      centralizer ({QuotientGroup.mk' V t} : Set (P ⧸ V))) = 2 :=
  le_antisymm (card_quot_le h) (card_quot_ge h hne)

theorem card_centralizer_eq [V.Normal] (h : PHyp S V t) (hne : S ≠ V) :
    Nat.card ↥(S ⊓ centralizer ({t} : Set P)) = 2 * Nat.card ↥(V ⊓ centralizer ({t} : Set P)) := by
  rw [card_eq_mul h, card_quot_eq h hne, mul_comm]

theorem PHyp.map_t_notMem [V.Normal] (h : PHyp S V t) :
    QuotientGroup.mk' V t ∉ S.map (QuotientGroup.mk' V) := by
  rintro ⟨s, hs, hst⟩
  have hv : s⁻¹ * t ∈ V := (QuotientGroup.eq).1 hst
  apply h.t_notMem
  have := S.mul_mem hs (h.V_le hv)
  simpa using this

theorem PHyp.index_map [V.Normal] (h : PHyp S V t) :
    (S.map (QuotientGroup.mk' V)).index = 2 := by
  rw [Subgroup.index_map_eq S (QuotientGroup.mk'_surjective V)
    (by rw [QuotientGroup.ker_mk']; exact h.V_le)]
  exact h.index_two

theorem PHyp.map_t_sq [V.Normal] (h : PHyp S V t) :
    QuotientGroup.mk' V t * QuotientGroup.mk' V t = 1 := by
  rw [← map_mul, h.t_sq, map_one]

theorem dihedral_or_semidihedral [V.Normal] (h : PHyp S V t) (hne : S ≠ V) :
    (∃ m : ℕ, 1 ≤ m ∧ Nonempty ((P ⧸ V) ≃* DihedralGroup (2 ^ m))) ∨
      ∃ k : ℕ, 4 ≤ k ∧ Nonempty ((P ⧸ V) ≃* SemidihedralGroup k) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 (P ⧸ V) := h.isPGroup.to_quotient V
  have ht1 : QuotientGroup.mk' V t ≠ 1 := by
    intro h1
    apply h.map_t_notMem
    rw [h1]
    exact one_mem _
  have ht2 : orderOf (QuotientGroup.mk' V t) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact h.map_t_sq) ht1
  have hsz := CFSG.Holt.suzuki_index_two (S := S.map (QuotientGroup.mk' V))
    (T := (⊤ : Subgroup (P ⧸ V))) (hQ.of_equiv Subgroup.topEquiv.symm) le_top
    (by rw [Subgroup.relIndex_top_right]; exact h.index_map) (Subgroup.mem_top _)
    h.map_t_notMem ht2 (card_quot_eq h hne)
  obtain ⟨-, hD | hSD⟩ := hsz
  · obtain ⟨m, hm, ⟨e⟩⟩ := hD
    exact Or.inl ⟨m, hm, ⟨Subgroup.topEquiv.symm.trans e⟩⟩
  · obtain ⟨k, hk, ⟨e⟩⟩ := hSD
    exact Or.inr ⟨k, hk, ⟨Subgroup.topEquiv.symm.trans e⟩⟩

theorem PHyp.exists_conj_of_map_conj [V.Normal] (h : PHyp S V t) {x y : P} (hy : y ∉ S)
    (hx2 : x * x = 1) (hy2 : y * y = 1)
    (hconj : ∃ u ∈ S.map (QuotientGroup.mk' V),
      u * QuotientGroup.mk' V y * u⁻¹ = QuotientGroup.mk' V x) : ∃ s ∈ S, s * y * s⁻¹ = x := by
  obtain ⟨u, ⟨s, hs, rfl⟩, hu⟩ := hconj
  have h1 : (QuotientGroup.mk' V) (s * y * s⁻¹) = (QuotientGroup.mk' V) x := by
    simpa [map_mul, map_inv] using hu
  have hv : (s * y * s⁻¹)⁻¹ * x ∈ V := (QuotientGroup.eq).1 h1
  have hy' : s * y * s⁻¹ ∉ S := by
    intro hmem
    apply hy
    have := S.mul_mem (S.mul_mem (S.inv_mem hs) hmem) hs
    simpa [mul_assoc] using this
  have hy'2 : (s * y * s⁻¹) * (s * y * s⁻¹) = 1 := by
    calc (s * y * s⁻¹) * (s * y * s⁻¹) = s * (y * y) * s⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  obtain ⟨w, hw, hwx⟩ := h.exists_conj_of_mem_coset hy' hy'2 hx2 hv
  refine ⟨w * s, S.mul_mem (h.V_le hw) hs, ?_⟩
  rw [hwx]
  group

theorem PHyp.map_notMem [V.Normal] (h : PHyp S V t) {x : P} (hx : x ∉ S) :
    QuotientGroup.mk' V x ∉ S.map (QuotientGroup.mk' V) := by
  rintro ⟨s, hs, hsx⟩
  have hv : s⁻¹ * x ∈ V := (QuotientGroup.eq).1 hsx
  apply hx
  have := S.mul_mem hs (h.V_le hv)
  simpa using this

theorem one_class_of_not_cyclic [V.Normal] (h : PHyp S V t) (hne : S ≠ V)
    (hcyc : ¬ IsCyclic ↥(S.map (QuotientGroup.mk' V))) {x : P} (hx : x ∉ S) (hx2 : x * x = 1) :
    ∃ s ∈ S, s * t * s⁻¹ = x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 (P ⧸ V) := h.isPGroup.to_quotient V
  obtain ⟨R, hR, hR2⟩ := exists_cyclic_index_two (dihedral_or_semidihedral h hne)
  set St := S.map (QuotientGroup.mk' V) with hSt
  have hS4 : 4 ≤ Nat.card St := by
    by_contra hlt
    push Not at hlt
    apply hcyc
    obtain ⟨k, hk⟩ := (hQ.to_subgroup St).exists_card_eq
    have hk1 : k ≤ 1 := by
      by_contra hk2
      push Not at hk2
      have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      omega
    apply isCyclic_of_card_dvd_prime (p := 2)
    rw [hk]
    interval_cases k <;> simp
  have hne' : St ≠ R := fun heq => hcyc (heq ▸ hR)
  have hq := conj_of_cyclic_index_two hQ hR hR2 h.index_map hne' hS4 h.map_t_notMem h.map_t_sq
    (card_quot_eq h hne) (x := QuotientGroup.mk' V x) (h.map_notMem hx)
    (by rw [← map_mul, hx2, map_one])
  exact h.exists_conj_of_map_conj h.t_notMem hx2 h.t_sq hq

theorem two_classes_of_cyclic [V.Normal] (h : PHyp S V t) (hne : S ≠ V)
    (hcyc : IsCyclic ↥(S.map (QuotientGroup.mk' V))) :
    ∃ b : P, b ∉ S ∧ b * b = 1 ∧ ∀ x : P, x ∉ S → x * x = 1 →
      (∃ u ∈ S, u * t * u⁻¹ = x) ∨ ∃ u ∈ S, u * b * u⁻¹ = x := by
  by_cases hall : ∀ x : P, x ∉ S → x * x = 1 → ∃ u ∈ S, u * t * u⁻¹ = x
  · exact ⟨t, h.t_notMem, h.t_sq, fun x hx hx2 => Or.inl (hall x hx hx2)⟩
  · push Not at hall
    obtain ⟨b, hb, hb2, hbt⟩ := hall
    have hbt' : ¬ ∃ u ∈ S, u * t * u⁻¹ = b := by
      rintro ⟨u, hu, hub⟩
      exact hbt u hu hub
    refine ⟨b, hb, hb2, fun x hx hx2 => ?_⟩
    by_contra hcon
    obtain ⟨hxt, hxb⟩ := not_or.1 hcon
    have hcomm : IsMulCommutative ↥(S.map (QuotientGroup.mk' V)) := inferInstance
    rcases two_orbits_of_abelian hcomm h.index_map h.map_t_notMem h.map_t_sq (card_quot_eq h hne)
      (x₁ := QuotientGroup.mk' V x) (x₂ := QuotientGroup.mk' V b) (x₃ := QuotientGroup.mk' V t)
      (h.map_notMem hx) (h.map_notMem hb) (h.map_notMem h.t_notMem) with h12 | h13 | h23
    · obtain ⟨s, hs, hsx⟩ := h.exists_conj_of_map_conj hx hb2 hx2 h12
      exact hxb ⟨s⁻¹, S.inv_mem hs, by rw [← hsx]; group⟩
    · obtain ⟨s, hs, hsx⟩ := h.exists_conj_of_map_conj hx h.t_sq hx2 h13
      exact hxt ⟨s⁻¹, S.inv_mem hs, by rw [← hsx]; group⟩
    · obtain ⟨s, hs, hsb⟩ := h.exists_conj_of_map_conj hb h.t_sq hb2 h23
      exact hbt' ⟨s⁻¹, S.inv_mem hs, by rw [← hsb]; group⟩

theorem exists_gen_of_cyclic [V.Normal] (h : PHyp S V t)
    (hcyc : IsCyclic ↥(S.map (QuotientGroup.mk' V))) : ∃ g ∈ S, S = zpowers g ⊔ V := by
  obtain ⟨c, hc⟩ := hcyc.exists_generator
  obtain ⟨g, hgS, hgc⟩ := c.2
  refine ⟨g, hgS, le_antisymm ?_ (sup_le (zpowers_le.2 hgS) h.V_le)⟩
  intro s hs
  obtain ⟨n, hn⟩ := hc ⟨QuotientGroup.mk' V s, ⟨s, hs, rfl⟩⟩
  have h1 : (QuotientGroup.mk' V) (g ^ n) = (QuotientGroup.mk' V) s := by
    have := congrArg Subtype.val hn
    simpa [map_zpow, hgc] using this
  have hv : (g ^ n)⁻¹ * s ∈ V := (QuotientGroup.eq).1 h1
  have : s = g ^ n * ((g ^ n)⁻¹ * s) := by group
  rw [this]
  exact Subgroup.mul_mem_sup (mem_zpowers_iff.2 ⟨n, rfl⟩) hv

end PLevel

end CFSG.LocalAnalysis.EvenBN.Tits.N.S16A
