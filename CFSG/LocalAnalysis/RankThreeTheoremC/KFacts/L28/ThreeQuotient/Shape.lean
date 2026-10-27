module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Shape

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.L28.ThreeQuotient

open CFSG.Open Subgroup

variable {G : Type} [Group G]

structure ShapeData (P Q₀ : Subgroup G) : Prop where
  card : Nat.card P = 3 ^ 5
  le : Q₀ ≤ P
  maximal : ∀ R : Subgroup G, Q₀ < R → R ≤ P → R = P
  card₀ : Nat.card Q₀ = 3 ^ 4
  comm₀ : ∀ a ∈ Q₀, ∀ b ∈ Q₀, a * b = b * a
  exp₀ : ∀ a ∈ Q₀, a ^ 9 = 1
  normal : ∀ g ∈ P, ∀ a ∈ Q₀, g * a * g⁻¹ ∈ Q₀
  central : ∀ a ∈ Q₀, a ^ 3 = 1 → ∀ g ∈ P, g * a = a * g
  center_le : ∀ a ∈ P, (∀ g ∈ P, g * a = a * g) → a ∈ Q₀ ∧ a ^ 3 = 1
  card_omega : Nat.card {a : G // a ∈ Q₀ ∧ a ^ 3 = 1} = 9
  cube_mem : ∀ g ∈ P, g ^ 3 ∈ Q₀
  coset : ∀ u ∈ P, ∀ v ∈ P, u ∉ Q₀ → v ∉ Q₀ → u⁻¹ * v ∈ Q₀ ∨ u * v ∈ Q₀
  exists_u : ∃ u ∈ P, u ∉ Q₀ ∧ u ^ 3 = 1

theorem eq_or_mul_eq_one_of_card_eq_three {H : Type*} [Group H] (hH : Nat.card H = 3)
    {α β : H} (hα : α ≠ 1) (hβ : β ≠ 1) : α = β ∨ α * β = 1 := by
  classical
  haveI : Finite H := Nat.finite_of_card_ne_zero (by omega)
  have hα3 : orderOf α = 3 := by
    have h1 : orderOf α ∣ 3 := hH ▸ orderOf_dvd_natCard α
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hα
    · exact h
  have htop : Subgroup.zpowers α = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hα3, hH]
  have hβmem : β ∈ Subgroup.zpowers α := htop ▸ Subgroup.mem_top β
  rw [mem_zpowers_iff_mem_range_orderOf, hα3] at hβmem
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hβmem
  have hk3 : k < 3 := Finset.mem_range.1 hk
  interval_cases k
  · exact absurd (pow_zero α) hβ
  · exact Or.inl (pow_one α).symm
  · refine Or.inr ?_
    have h3 : α ^ 3 = 1 := hα3 ▸ pow_orderOf_eq_one α
    calc α * α ^ 2 = α ^ 3 := by rw [pow_two, pow_three]
      _ = 1 := h3

theorem L28Shape.shapeData {P : Subgroup G} (h : L28Shape 3 P) : ∃ Q₀ : Subgroup G,
    ShapeData P Q₀ := by
  classical
  obtain ⟨hcard, Q₀, hlt, hmax, ⟨e⟩, ⟨C, hCP, hQC, hQCP⟩, ⟨A, B, -, -, -, hABQ, hPA, hPB⟩,
    hZ⟩ := h
  have hle : Q₀ ≤ P := hlt.le
  have hMcard : Nat.card (Multiplicative (ZMod (3 ^ 2)) × Multiplicative (ZMod (3 ^ 2))) = 81 := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    norm_num
  have hM9 : ∀ y : Multiplicative (ZMod (3 ^ 2)) × Multiplicative (ZMod (3 ^ 2)), y ^ 9 = 1 := by
    decide
  have hMΩ : Nat.card {y : Multiplicative (ZMod (3 ^ 2)) × Multiplicative (ZMod (3 ^ 2)) //
      y ^ 3 = 1} = 9 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hcard₀ : Nat.card Q₀ = 3 ^ 4 := by
    rw [Nat.card_congr e.toEquiv, hMcard]
    norm_num
  have hcomm₀ : ∀ a ∈ Q₀, ∀ b ∈ Q₀, a * b = b * a := by
    intro a ha b hb
    have h1 : (⟨a, ha⟩ * ⟨b, hb⟩ : Q₀) = ⟨b, hb⟩ * ⟨a, ha⟩ :=
      e.injective (by rw [map_mul, map_mul, mul_comm])
    simpa using congrArg Subtype.val h1
  have hexp₀ : ∀ a ∈ Q₀, a ^ 9 = 1 := by
    intro a ha
    have h1 : (⟨a, ha⟩ : Q₀) ^ 9 = 1 := e.injective (by rw [map_pow, map_one, hM9])
    simpa using congrArg Subtype.val h1
  have hnormal : ∀ g ∈ P, ∀ a ∈ Q₀, g * a * g⁻¹ ∈ Q₀ := by
    intro g hg a ha
    have hsub : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · have h1 := (Subgroup.mem_normalizer_iff.1 (hPA hg) x).1 hx
        exact Subgroup.mem_sup_left (by simpa [MulAut.conj_apply] using h1)
      · have h1 := (Subgroup.mem_normalizer_iff.1 (hPB hg) x).1 hx
        exact Subgroup.mem_sup_right (by simpa [MulAut.conj_apply] using h1)
    rw [← hABQ] at ha ⊢
    simpa [MulAut.conj_apply] using hsub ha
  have hcentral : ∀ a ∈ Q₀, a ^ 3 = 1 → ∀ g ∈ P, g * a = a * g := by
    intro a ha ha3 g hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ((hZ a).2 ⟨ha, ha3⟩)
    have h1 := Subgroup.mem_center_iff.1 hx ⟨g, hg⟩
    simpa using congrArg Subtype.val h1
  have hcenter : ∀ a ∈ P, (∀ g ∈ P, g * a = a * g) → a ∈ Q₀ ∧ a ^ 3 = 1 := by
    intro a ha hcomm
    have hx : (⟨a, ha⟩ : P) ∈ center P :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (hcomm g g.2)
    exact (hZ a).1 ⟨⟨a, ha⟩, hx, rfl⟩
  have hΩ : Nat.card {a : G // a ∈ Q₀ ∧ a ^ 3 = 1} = 9 := by
    let f : {a : G // a ∈ Q₀ ∧ a ^ 3 = 1} ≃ {x : Q₀ // (x : G) ^ 3 = 1} :=
      { toFun := fun a => ⟨⟨a.1, a.2.1⟩, a.2.2⟩
        invFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
        left_inv := fun a => rfl
        right_inv := fun x => rfl }
    have hiff : ∀ x : Q₀, (x : G) ^ 3 = 1 ↔ e x ^ 3 = 1 := by
      intro x
      rw [← map_pow, ← map_one e, e.injective.eq_iff, ← Subtype.val_inj]
      simp
    rw [Nat.card_congr (f.trans (e.toEquiv.subtypeEquiv (q := fun y => y ^ 3 = 1)
      fun x => hiff x)), hMΩ]
  haveI hN : (Q₀.subgroupOf P).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hnormal g g.2 n hn⟩
  have hQcard : Nat.card (P ⧸ Q₀.subgroupOf P) = 3 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Q₀.subgroupOf P)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard, hcard₀] at h1
    omega
  have hcube : ∀ g ∈ P, g ^ 3 ∈ Q₀ := by
    intro g hg
    have h1 : ((⟨g, hg⟩ : P) : P ⧸ Q₀.subgroupOf P) ^ 3 = 1 := by
      rw [← hQcard]
      exact pow_card_eq_one'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have hcoset : ∀ u ∈ P, ∀ v ∈ P, u ∉ Q₀ → v ∉ Q₀ → u⁻¹ * v ∈ Q₀ ∨ u * v ∈ Q₀ := by
    intro u hu v hv hu0 hv0
    have hne : ∀ w (hw : w ∈ P), w ∉ Q₀ → ((⟨w, hw⟩ : P) : P ⧸ Q₀.subgroupOf P) ≠ 1 := by
      intro w hw hw0 h1
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      exact hw0 h1
    rcases eq_or_mul_eq_one_of_card_eq_three hQcard (hne u hu hu0) (hne v hv hv0) with h1 | h1
    · left
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
      simpa using h1
    · right
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      simpa using h1
  have hu : ∃ u ∈ P, u ∉ Q₀ ∧ u ^ 3 = 1 := by
    have hC : C ≠ ⊥ := by
      rintro rfl
      rw [sup_bot_eq] at hQCP
      exact hlt.ne hQCP
    obtain ⟨⟨c, hcC⟩, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hC
    have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
    have hcP : c ∈ P := hCP hcC
    refine ⟨c, hcP, fun hc0 => hc1' ?_, ?_⟩
    · have : c ∈ Q₀ ⊓ C := ⟨hc0, hcC⟩
      rwa [hQC, Subgroup.mem_bot] at this
    · have : c ^ 3 ∈ Q₀ ⊓ C := ⟨hcube c hcP, pow_mem hcC 3⟩
      rwa [hQC, Subgroup.mem_bot] at this
  exact ⟨Q₀, ⟨hcard, hle, hmax, hcard₀, hcomm₀, hexp₀, hnormal, hcentral, hcenter, hΩ, hcube,
    hcoset, hu⟩⟩

theorem mul_pow_three_aux {a c : G} (h : c * a = a * c) :
    a * c * c * (a * c) * a = a ^ 3 * c ^ 3 := by
  have h2 : c * c * a = a * (c * c) := by
    rw [mul_assoc, h, ← mul_assoc, h, mul_assoc]
  calc a * c * c * (a * c) * a = a * (c * c * a) * (c * a) := by group
    _ = a * (a * (c * c)) * (a * c) := by rw [h2, h]
    _ = a * a * (c * c * a) * c := by group
    _ = a * a * (a * (c * c)) * c := by rw [h2]
    _ = a ^ 3 * c ^ 3 := by rw [pow_three, pow_three]; simp only [mul_assoc]

namespace ShapeData

variable {P Q₀ : Subgroup G}

theorem cube_mul (hD : ShapeData P Q₀) {x a : G} (hx : x ∈ P) (ha : a ∈ Q₀) :
    (x * a) ^ 3 = x ^ 3 * a ^ 3 := by
  have hb : x⁻¹ * a * x ∈ Q₀ := by
    simpa using hD.normal x⁻¹ (inv_mem hx) a ha
  set c := a⁻¹ * (x⁻¹ * a * x) with hc
  have hcQ : c ∈ Q₀ := mul_mem (inv_mem ha) hb
  have hbac : x⁻¹ * a * x = a * c := by rw [hc]; group
  have ha33 : (a ^ 3) ^ 3 = 1 := by rw [← pow_mul]; exact hD.exp₀ a ha
  have hcen3 := hD.central (a ^ 3) (pow_mem ha 3) ha33 x⁻¹ (inv_mem hx)
  have hc3 : c ^ 3 = 1 := by
    have hcomm : Commute a⁻¹ (x⁻¹ * a * x) := hD.comm₀ _ (inv_mem ha) _ hb
    have hconj : (x⁻¹ * a * x) ^ 3 = x⁻¹ * a ^ 3 * x := by
      have := conj_pow (a := x⁻¹) (b := a) (i := 3)
      simpa using this
    rw [hc, hcomm.mul_pow, hconj, hcen3]
    group
  have hcen := hD.central c hcQ hc3
  have hxc : x⁻¹ * c * x = c := by
    rw [hcen x⁻¹ (inv_mem hx)]
    group
  have hca : c * a = a * c := (hcen a (hD.le ha)).symm
  have hd : x⁻¹ * (x⁻¹ * a * x) * x = a * c * c := by
    calc x⁻¹ * (x⁻¹ * a * x) * x = x⁻¹ * (a * c) * x := by rw [hbac]
      _ = (x⁻¹ * a * x) * (x⁻¹ * c * x) := by group
      _ = a * c * c := by rw [hbac, hxc]
  calc (x * a) ^ 3 = x ^ 3 * (x⁻¹ * (x⁻¹ * a * x) * x) * (x⁻¹ * a * x) * a := by
        simp only [pow_three]; group
    _ = x ^ 3 * (a * c * c * (a * c) * a) := by rw [hd, hbac]; group
    _ = x ^ 3 * a ^ 3 := by rw [mul_pow_three_aux hca, hc3, mul_one]

theorem omega_comm (hD : ShapeData P Q₀) {u v : G} (hu : u ∈ P) (hv : v ∈ P) (hu3 : u ^ 3 = 1)
    (hv3 : v ^ 3 = 1) : u * v = v * u := by
  by_cases hu0 : u ∈ Q₀
  · exact (hD.central u hu0 hu3 v hv).symm
  by_cases hv0 : v ∈ Q₀
  · exact hD.central v hv0 hv3 u hu
  rcases hD.coset u hu v hv hu0 hv0 with h | h
  · have hva : v = u * (u⁻¹ * v) := by group
    have h3 := hD.cube_mul hu h
    rw [← hva, hv3, hu3, one_mul] at h3
    have hc := hD.central _ h h3.symm u hu
    rw [hva, mul_assoc, ← hc]
  · have hva : v = u⁻¹ * (u * v) := by group
    have h3 := hD.cube_mul (inv_mem hu) h
    have hu3' : u⁻¹ ^ 3 = 1 := by rw [inv_pow, hu3, inv_one]
    rw [← hva, hv3, hu3', one_mul] at h3
    have hc := hD.central _ h h3.symm u hu
    calc u * v = u * v := rfl
      _ = u⁻¹ * (u * (u * v)) := by group
      _ = u⁻¹ * ((u * v) * u) := by rw [hc]
      _ = v * u := by group

theorem relIndex_eq (hD : ShapeData P Q₀) : Q₀.relIndex P = 3 := by
  have h1 := Subgroup.relIndex_mul_card Q₀ P
  rw [inf_eq_left.2 hD.le, hD.card, hD.card₀] at h1
  omega

theorem relIndex_le (hD : ShapeData P Q₀) {F : Subgroup G} (hF : F ≤ P) :
    Q₀.relIndex F ≤ 3 := by
  rw [← hD.relIndex_eq]
  exact Subgroup.relIndex_le_of_le_right hF (by rw [hD.relIndex_eq]; norm_num)

theorem card_le_nine (hD : ShapeData P Q₀) {F : Subgroup G} (hF : ∀ a ∈ F, a ∈ Q₀ ∧ a ^ 3 = 1) :
    Nat.card F ≤ 9 := by
  have hfin : Finite {a : G // a ∈ Q₀ ∧ a ^ 3 = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hD.card_omega]; norm_num)
  rw [← hD.card_omega]
  refine Nat.card_le_card_of_injective (fun a => ⟨a.1, hF a.1 a.2⟩) ?_
  intro a b hab
  apply Subtype.ext
  have h1 := congrArg Subtype.val hab
  simpa using h1

theorem exists_omega (hD : ShapeData P Q₀) :
    ∃ E : Subgroup G, E ≤ P ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧
      ∀ v ∈ P, v ^ 3 = 1 → v ∈ E := by
  let E : Subgroup G :=
    { carrier := {v | v ∈ P ∧ v ^ 3 = 1}
      mul_mem' := fun {v w} hv hw => ⟨mul_mem hv.1 hw.1, by
        rw [(Commute.mul_pow (hD.omega_comm hv.1 hw.1 hv.2 hw.2) 3), hv.2, hw.2, one_mul]⟩
      one_mem' := ⟨one_mem P, one_pow 3⟩
      inv_mem' := fun {v} hv => ⟨inv_mem hv.1, by rw [inv_pow, hv.2, inv_one]⟩ }
  have hEP : E ≤ P := fun v hv => hv.1
  refine ⟨E, hEP, ⟨⟨⟨fun a b => Subtype.ext (hD.omega_comm a.2.1 b.2.1 a.2.2 b.2.2)⟩⟩,
    fun v hv => hv.2⟩, ?_, fun v hv hv3 => ⟨hv, hv3⟩⟩
  have h1 := Subgroup.relIndex_mul_card Q₀ E
  have h9 : Nat.card (Q₀ ⊓ E : Subgroup G) = 9 := by
    rw [← hD.card_omega]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
    change a ∈ Q₀ ∧ (a ∈ P ∧ a ^ 3 = 1) ↔ a ∈ Q₀ ∧ a ^ 3 = 1
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hD.le h.1, h.2⟩⟩
  rw [h9] at h1
  have hle3 := hD.relIndex_le hEP
  have hne1 : Q₀.relIndex E ≠ 1 := by
    intro h
    obtain ⟨u, huP, hu0, hu3⟩ := hD.exists_u
    exact hu0 ((Subgroup.relIndex_eq_one.1 h) ⟨huP, hu3⟩)
  have hdvd : Nat.card E ∣ 3 ^ 5 := hD.card ▸ Subgroup.card_dvd_of_le hEP
  rw [← h1] at hdvd ⊢
  interval_cases hr : Q₀.relIndex E
  · norm_num at hdvd
  · omega
  · norm_num at hdvd
  · norm_num

theorem card_le_of_isElemAbelian (hD : ShapeData P Q₀) {F : Subgroup G} (hFP : F ≤ P)
    (hF : IsElemAbelian 3 F) : Nat.card F ≤ 27 := by
  have h1 := Subgroup.relIndex_mul_card Q₀ F
  have h9 : Nat.card (Q₀ ⊓ F : Subgroup G) ≤ 9 :=
    hD.card_le_nine fun a ha => ⟨ha.1, hF.2 a ha.2⟩
  have h3 := hD.relIndex_le hFP
  rw [← h1]
  calc Q₀.relIndex F * Nat.card (Q₀ ⊓ F : Subgroup G) ≤ 3 * 9 := Nat.mul_le_mul h3 h9
    _ = 27 := by norm_num

theorem not_comm (hD : ShapeData P Q₀) : ¬ ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  intro h
  obtain ⟨u, huP, hu0, -⟩ := hD.exists_u
  exact hu0 (hD.center_le u huP fun g hg => h g hg u huP).1

theorem eq_of_comm (hD : ShapeData P Q₀) {M : Subgroup G} (hMP : M ≤ P)
    (hM : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a) (hcard : Nat.card M = 3 ^ 4) : M = Q₀ := by
  haveI : Finite Q₀ := Nat.finite_of_card_ne_zero (by rw [hD.card₀]; norm_num)
  by_contra hne
  have hnle : ¬ M ≤ Q₀ := fun hle =>
    hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hD.card₀, hcard]))
  obtain ⟨m, hmM, hm0⟩ := SetLike.not_le_iff_exists.1 hnle
  have hcen : ∀ z ∈ Q₀ ⊓ M, z ∈ Q₀ ∧ z ^ 3 = 1 := by
    intro z hz
    refine hD.center_le z (hD.le hz.1) ?_
    let R : Subgroup G := Subgroup.centralizer ({z} : Set G) ⊓ P
    have hQR : Q₀ ≤ R := fun a ha =>
      ⟨Subgroup.mem_centralizer_singleton_iff.2 (hD.comm₀ z hz.1 a ha).symm, hD.le ha⟩
    have hmR : m ∈ R :=
      ⟨Subgroup.mem_centralizer_singleton_iff.2 (hM z hz.2 m hmM).symm, hMP hmM⟩
    have hRP : R = P := hD.maximal R (lt_of_le_of_ne hQR fun h => hm0 (h ▸ hmR)) inf_le_right
    intro g hg
    have hgR : g ∈ R := hRP ▸ hg
    exact Subgroup.mem_centralizer_singleton_iff.1 hgR.1
  have h9 := hD.card_le_nine hcen
  have h1 := Subgroup.relIndex_mul_card Q₀ M
  have h3 := hD.relIndex_le hMP
  rw [hcard] at h1
  have : 81 ≤ 3 * 9 := by
    calc 81 = Q₀.relIndex M * Nat.card (Q₀ ⊓ M : Subgroup G) := by rw [h1]; norm_num
      _ ≤ 3 * 9 := Nat.mul_le_mul h3 h9
  omega

theorem conj_mem (hD : ShapeData P Q₀) {g : G} (hg : g ∈ Subgroup.normalizer (P : Set G))
    {a : G} (ha : a ∈ Q₀) : g * a * g⁻¹ ∈ Q₀ := by
  have hM : Q₀.map (MulAut.conj g).toMonoidHom = Q₀ := by
    refine hD.eq_of_comm ?_ ?_ ?_
    · rintro _ ⟨b, hb, rfl⟩
      have := (Subgroup.mem_normalizer_iff.1 hg b).1 (hD.le hb)
      simpa [MulAut.conj_apply] using this
    · rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hD.comm₀ b hb b' hb']
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hD.card₀]
  rw [← hM]
  exact ⟨a, ha, by simp [MulAut.conj_apply]⟩

end ShapeData

end CFSG.LocalAnalysis.RankThreeTheoremC.L28.ThreeQuotient
