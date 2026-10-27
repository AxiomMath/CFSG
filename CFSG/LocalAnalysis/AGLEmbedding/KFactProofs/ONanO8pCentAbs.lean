module

public import CFSG.Assembly.Defs
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.AGLEmbedding.O8pCent

open CFSG.Assembly (IsElemAbelian)

private theorem card_eq_card_inf_ker_mul_card_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    (K : Subgroup G) : Nat.card K = Nat.card ↥(K ⊓ f.ker) * Nat.card ↥(K.map f) := by
  have h1 := Subgroup.card_mul_index (f.comp K.subtype).ker
  rw [Subgroup.index_ker, MonoidHom.range_comp, Subgroup.range_subtype] at h1
  rw [← h1]
  congr 1
  have : (f.comp K.subtype).ker = (f.ker).subgroupOf K := (MonoidHom.comap_ker f K.subtype).symm
  rw [this, ← Subgroup.card_map_of_injective K.subtype_injective,
    Subgroup.subgroupOf_map_subtype, inf_comm]

theorem card_le_card_fixed_pow_three {G : Type*} [CommGroup G] [Finite G]
    (hexp : ∀ x : G, x ^ 3 = 1) (φ : G →* G) (hφ3 : ∀ x, φ (φ (φ x)) = x) {F : Subgroup G}
    (hF : ∀ x, x ∈ F ↔ φ x = x) : Nat.card G ≤ Nat.card F ^ 3 := by
  let d : G →* G := MonoidHom.mk' (fun x => x⁻¹ * φ x) fun a b => by
    rw [mul_inv_rev, map_mul, mul_comm b⁻¹ a⁻¹, mul_mul_mul_comm]
  have hd : ∀ x, d x = x⁻¹ * φ x := fun x => rfl
  have hd2 : ∀ x, d (d x) = x * φ x * φ (φ x) := by
    intro x
    have hb : (φ x)⁻¹ * (φ x)⁻¹ = φ x := by
      calc (φ x)⁻¹ * (φ x)⁻¹ = (φ x)⁻¹ * (φ x)⁻¹ * (φ x) ^ 3 := by rw [hexp, mul_one]
        _ = φ x := by group
    rw [hd, hd, map_mul, map_inv, mul_inv_rev, inv_inv, mul_comm (φ x)⁻¹ x, mul_assoc,
      ← mul_assoc (φ x)⁻¹, hb, ← mul_assoc]
  have hs : ∀ x, φ (x * φ x * φ (φ x)) = x * φ x * φ (φ x) := by
    intro x
    rw [map_mul, map_mul, hφ3, mul_comm (φ x * φ (φ x)) x, mul_assoc]
  have hd3 : ∀ x, d (d (d x)) = 1 := by
    intro x
    calc d (d (d x)) = d (x * φ x * φ (φ x)) := congrArg d (hd2 x)
      _ = (x * φ x * φ (φ x))⁻¹ * φ (x * φ x * φ (φ x)) := hd _
      _ = 1 := by rw [hs, inv_mul_cancel]
  have hker : d.ker = F := by
    ext x
    rw [MonoidHom.mem_ker, hd, inv_mul_eq_one, hF]
    exact eq_comm
  rw [← hker]
  have h1 := Subgroup.card_ker_mul_card_range d
  have h2 := card_eq_card_inf_ker_mul_card_map d d.range
  have h3 : Nat.card ↥(d.range ⊓ d.ker) ≤ Nat.card d.ker := Subgroup.card_le_of_le inf_le_right
  have h4 : d.range.map d ≤ d.ker := by
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    rw [MonoidHom.mem_ker]
    exact hd3 y
  have h5 : Nat.card ↥(d.range.map d) ≤ Nat.card d.ker := Subgroup.card_le_of_le h4
  calc Nat.card G = Nat.card d.ker * Nat.card d.range := h1.symm
    _ ≤ Nat.card d.ker * (Nat.card d.ker * Nat.card d.ker) :=
        Nat.mul_le_mul_left _ (h2.trans_le (Nat.mul_le_mul h3 h5))
    _ = Nat.card d.ker ^ 3 := by ring

theorem exists_fixed_elemAbelian_nine {J : Type*} [Group J] {D : Subgroup J}
    (hD : IsElemAbelian 3 D) (h81 : Nat.card D = 81) {α : MulAut J} (hα : α ^ 3 = 1)
    (hαD : ∀ x ∈ D, α x ∈ D) :
    ∃ E : Subgroup J, E ≤ D ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ ∀ x ∈ E, α x = x := by
  classical
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [h81]; norm_num)
  have hcomm : ∀ a b : D, a * b = b * a := fun a b => hD.1.is_comm.comm a b
  let _ : CommGroup D := { (inferInstance : Group D) with mul_comm := hcomm }
  have hexp : ∀ x : D, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hD.2 x.1 x.2)
  let φ : D →* D := MonoidHom.mk' (fun x => ⟨α x, hαD x x.2⟩) fun a b =>
    Subtype.ext (map_mul α (a : J) (b : J))
  have hφ : ∀ x : D, (φ x : J) = α x := fun x => rfl
  have hφ3 : ∀ x : D, φ (φ (φ x)) = x := by
    intro x
    apply Subtype.ext
    rw [hφ, hφ, hφ]
    have := congrArg (fun β : MulAut J => β (x : J)) hα
    simpa [pow_succ, MulAut.mul_apply] using this
  let F : Subgroup D :=
    { carrier := {x | φ x = x}
      mul_mem' := fun {a b} (ha : φ a = a) (hb : φ b = b) => by
        show φ (a * b) = a * b
        rw [map_mul, ha, hb]
      one_mem' := map_one φ
      inv_mem' := fun {a} (ha : φ a = a) => by
        show φ a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hF : ∀ x, x ∈ F ↔ φ x = x := fun x => Iff.rfl
  have hcard := card_le_card_fixed_pow_three hexp φ hφ3 hF
  rw [h81] at hcard
  have hFdvd : Nat.card F ∣ 3 ^ 4 := by
    have := Subgroup.card_subgroup_dvd_card F
    rwa [h81, show (81 : ℕ) = 3 ^ 4 by norm_num] at this
  obtain ⟨k, hk, hkF⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hFdvd
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have : k ≤ 1 := by omega
    have h3 : Nat.card F ≤ 3 := by
      rw [hkF]
      calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
        _ = 3 := by norm_num
    have : Nat.card F ^ 3 ≤ 3 ^ 3 := Nat.pow_le_pow_left h3 3
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := F) (n := 2)
    (by rw [hkF]; exact pow_dvd_pow 3 hk2)
  set E₀ : Subgroup D := K.map F.subtype with hE₀
  have hE₀F : E₀ ≤ F := Subgroup.map_subtype_le K
  set E : Subgroup J := E₀.map D.subtype with hE
  have hED : E ≤ D := Subgroup.map_subtype_le E₀
  refine ⟨E, hED, ⟨⟨⟨fun a b => Subtype.ext (by
      simpa using congrArg Subtype.val (hD.1.is_comm.comm ⟨a, hED a.2⟩ ⟨b, hED b.2⟩))⟩⟩,
      fun x hx => hD.2 x (hED hx)⟩, ?_, ?_⟩
  · rw [hE, Subgroup.card_map_of_injective D.subtype_injective, hE₀,
      Subgroup.card_map_of_injective F.subtype_injective, hK]
    norm_num
  · rintro _ ⟨y, hy, rfl⟩
    have := (hF y).1 (hE₀F hy)
    exact congrArg Subtype.val this

theorem eq_of_card_eq_81 {G : Type*} [Group G] [Finite G] {Q D A : Subgroup G} {g : G}
    (hQ : Nat.card Q = 243) (hDQ : D ≤ Q) (hD : IsMulCommutative D) (hD81 : Nat.card D = 81)
    (hgQ : g ∈ Q)
    (hC : ∀ C : Subgroup G, C ≤ D → (∀ c ∈ C, g * c = c * g) → Nat.card C ≤ 9)
    (hAQ : A ≤ Q) (hA : IsMulCommutative A) (hA81 : Nat.card A = 81) : A = D := by
  by_contra hne
  have hrelQ : D.relIndex Q = 3 := by
    have h := Subgroup.relIndex_mul_card D Q
    rw [inf_eq_left.2 hDQ, hD81, hQ] at h
    omega
  have hrelA : D.relIndex A ≤ 3 :=
    (Subgroup.relIndex_le_of_le_right hAQ (by rw [hrelQ]; norm_num)).trans hrelQ.le
  have h27 : 27 ≤ Nat.card ↥(D ⊓ A) := by
    have h := Subgroup.relIndex_mul_card D A
    rw [hA81] at h
    generalize D.relIndex A = r at h hrelA
    generalize Nat.card ↥(D ⊓ A) = m at h ⊢
    interval_cases r <;> omega
  have hAD : ¬ A ≤ D := fun h => hne (Subgroup.eq_of_le_of_card_ge h (by rw [hA81, hD81]))
  have hsup : A ⊔ D = Q := by
    have hle : A ⊔ D ≤ Q := sup_le hAQ hDQ
    have h1 : Nat.card D ∣ Nat.card ↥(A ⊔ D) := Subgroup.card_dvd_of_le le_sup_right
    have h2 : Nat.card ↥(A ⊔ D) ∣ Nat.card Q := Subgroup.card_dvd_of_le hle
    rw [hD81] at h1
    rw [hQ] at h2
    obtain ⟨c, hc⟩ := h1
    have hc3 : c ∣ 3 := by
      have : 81 * c ∣ 81 * 3 := by rw [← hc]; exact h2
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    rcases (Nat.dvd_prime Nat.prime_three).1 hc3 with rfl | rfl
    · exfalso
      apply hAD
      have : D = A ⊔ D := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hD81]; omega)
      exact le_sup_left.trans this.ge
    · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hQ]; omega)
  have hcomm : ∀ x ∈ D ⊓ A, g * x = x * g := by
    intro x hx
    have hxA : x ∈ A := hx.2
    have hxD : x ∈ D := hx.1
    have hle : A ⊔ D ≤ Subgroup.centralizer {x} := by
      refine sup_le (fun a ha => ?_) (fun d hd => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact hA.is_comm.comm ⟨x, hxA⟩ ⟨a, ha⟩ |> congrArg Subtype.val
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact hD.is_comm.comm ⟨x, hxD⟩ ⟨d, hd⟩ |> congrArg Subtype.val
    rw [← hsup] at hgQ
    exact (Subgroup.mem_centralizer_iff.1 (hle hgQ) x (Set.mem_singleton x)).symm
  have := hC (D ⊓ A) inf_le_left hcomm
  omega

theorem exists_sylow_map_eq {J : Type*} [Group J] [Finite J] {α : MulAut J} (hα : α ^ 3 = 1) :
    ∃ R : Sylow 3 J, (R : Subgroup J).map α.toMonoidHom = R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let H : Subgroup (MulAut J) := Subgroup.zpowers α
  have hH : IsPGroup 3 H := by
    intro x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 x.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hα, one_zpow]
    rfl
  have h1 := hH.card_modEq_card_fixedPoints (Sylow 3 J)
  have h2 := card_sylow_modEq_one 3 J
  have h3 : Nat.card (MulAction.fixedPoints H (Sylow 3 J)) ≡ 1 [MOD 3] := h1.symm.trans h2
  have hne : (MulAction.fixedPoints H (Sylow 3 J)).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp] at h3
    simp [Nat.ModEq] at h3
  obtain ⟨R, hR⟩ := hne
  refine ⟨R, ?_⟩
  have hαR : (⟨α, Subgroup.mem_zpowers α⟩ : H) • R = R := hR ⟨α, Subgroup.mem_zpowers α⟩
  have := congrArg (fun P : Sylow 3 J => (P : Subgroup J)) hαR
  have h4 : Subgroup.map (MulDistribMulAction.toMonoidHom J α) (R : Subgroup J) = R := by
    simpa [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] using this
  exact h4

theorem isElemAbelian_map_hom {G H : Type*} [Group G] [Group H] (f : G →* H) {E : Subgroup G}
    (hE : IsElemAbelian 3 E) : IsElemAbelian 3 (E.map f) := CFSG.Open.IsElemAbelian.map hE _

theorem exists_fixed_elemAbelian_nine_of_sylow {J : Type*} [Group J] [Finite J]
    {Q D : Subgroup J} {g : J} (hQ : Nat.card Q = 3 ^ (Nat.card J).factorization 3)
    (hQ243 : Nat.card Q = 243) (hDQ : D ≤ Q) (hD : IsElemAbelian 3 D) (hD81 : Nat.card D = 81)
    (hgQ : g ∈ Q) (hC : ∀ C : Subgroup J, C ≤ D → (∀ c ∈ C, g * c = c * g) → Nat.card C ≤ 9)
    {α : MulAut J} (hα : α ^ 3 = 1) :
    ∃ E : Subgroup J, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ ∀ x ∈ E, α x = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hR⟩ := exists_sylow_map_eq hα
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq J (Sylow.ofCard Q hQ) R
  set c : MulAut J := MulAut.conj x with hc
  have hRQ : (R : Subgroup J) = Q.map c.toMonoidHom := by
    rw [← hx, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hRα : ∀ z ∈ (R : Subgroup J), α z ∈ (R : Subgroup J) := fun z hz => by
    rw [← hR]
    exact Subgroup.mem_map_of_mem α.toMonoidHom hz
  set α' : MulAut J := c⁻¹ * α * c with hα'
  have hα'3 : α' ^ 3 = 1 := by
    calc α' ^ 3 = c⁻¹ * α ^ 3 * c := by rw [hα', pow_three, pow_three α]; group
      _ = 1 := by rw [hα]; group
  have hα'apply : ∀ y, α' y = c.symm (α (c y)) := fun y => rfl
  have hα'Q : ∀ y ∈ Q, α' y ∈ Q := by
    intro y hy
    have h1 : c y ∈ (R : Subgroup J) := by
      rw [hRQ]
      exact Subgroup.mem_map_of_mem c.toMonoidHom hy
    have h2 := hRα _ h1
    rw [hRQ] at h2
    obtain ⟨y', hy', hy'c⟩ := h2
    rw [hα'apply, ← hy'c]
    simpa using hy'
  set A : Subgroup J := D.map α'.toMonoidHom with hA
  have hAQ : A ≤ Q := by
    rintro _ ⟨a, ha, rfl⟩
    exact hα'Q a (hDQ ha)
  have hA81 : Nat.card A = 81 := by
    rw [hA, Subgroup.card_map_of_injective α'.injective, hD81]
  have hAD : A = D :=
    eq_of_card_eq_81 hQ243 hDQ hD.1 hD81 hgQ hC hAQ (isElemAbelian_map_hom α'.toMonoidHom hD).1 hA81
  have hα'D : ∀ y ∈ D, α' y ∈ D := fun y hy => by
    rw [← hAD]
    exact Subgroup.mem_map_of_mem α'.toMonoidHom hy
  obtain ⟨E', -, hE'e, hE'9, hE'fix⟩ := exists_fixed_elemAbelian_nine hD hD81 hα'3 hα'D
  refine ⟨E'.map c.toMonoidHom, isElemAbelian_map_hom c.toMonoidHom hE'e, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective c.injective, hE'9]
  · rintro _ ⟨e, he, rfl⟩
    have h1 := hE'fix e he
    rw [hα'apply] at h1
    exact (MulEquiv.eq_symm_apply c).1 h1.symm |>.symm

end CFSG.AGLEmbedding.O8pCent
