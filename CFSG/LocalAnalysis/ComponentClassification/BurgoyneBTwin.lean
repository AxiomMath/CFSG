module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBLift
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPropALift

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open CFSG Subgroup CFSG.ComponentClassification.TBLit
open scoped commutatorElement MatrixGroups

variable {Q : Type} [Group Q]

theorem mem_sup_of_commute {A C : Subgroup Q} (h : ∀ a ∈ A, ∀ b ∈ C, a * b = b * a) {x : Q} :
    x ∈ A ⊔ C ↔ ∃ a ∈ A, ∃ b ∈ C, a * b = x := by
  constructor
  · intro hx
    let M : Subgroup Q :=
      { carrier := {x | ∃ a ∈ A, ∃ b ∈ C, a * b = x}
        one_mem' := ⟨1, one_mem _, 1, one_mem _, mul_one 1⟩
        mul_mem' := by
          rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
          refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
          calc a * a' * (b * b') = a * (a' * b) * b' := by group
            _ = a * (b * a') * b' := by rw [h a' ha' b hb]
            _ = a * b * (a' * b') := by group
        inv_mem' := by
          rintro _ ⟨a, ha, b, hb, rfl⟩
          refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
          rw [mul_inv_rev, h a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)] }
    have hle : A ⊔ C ≤ M := sup_le (fun a ha => ⟨a, ha, 1, one_mem _, mul_one a⟩)
      (fun b hb => ⟨1, one_mem _, b, hb, one_mul b⟩)
    exact hle hx
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact mul_mem (mem_sup_left ha) (mem_sup_right hb)

theorem commutator_eq_bot_of_le_center {A C : Subgroup Q} (hA : ⁅A, A⁆ = A)
    (hAC : ⁅A, C⁆ ≤ center Q) : ⁅A, C⁆ = ⊥ := by
  have h1 : ⁅⁅A, C⁆, A⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro y _
    exact (mem_center_iff.mp (hAC hx) y)
  have h2 : ⁅⁅C, A⁆, A⁆ = ⊥ := by
    rw [commutator_comm C A]
    exact h1
  have := commutator_commutator_eq_bot_of_rotate h1 h2
  rwa [hA] at this

variable {B : Type} [Group B] [Finite Q] (σ : Q →* B)

theorem twin_of_lift (hker : σ.ker ≤ center Q) (hker2 : IsPGroup 2 σ.ker)
    {S₁ S₂ : Subgroup B} (hS₁r : S₁ ≤ σ.range) (hS₂r : S₂ ≤ σ.range)
    {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ n)
    (e₁ : S₁ ≃* SL(2, GaloisField p n)) (e₂ : S₂ ≃* SL(2, GaloisField p n))
    (hcomm : ∀ a ∈ S₁, ∀ b ∈ S₂, a * b = b * a) {ū : B} (hū : orderOf ū = 2) (hū₁ : ū ∈ S₁)
    (hū₂ : ū ∈ S₂) (hint : ∀ x, x ∈ S₁ → x ∈ S₂ → x = 1 ∨ x = ū)
    {c : Q} (hc : σ c = 1) (hc1 : c ≠ 1)
    (hcT : c ∈ ⁅S₁.comap σ, S₁.comap σ⁆ ⊔ ⁅S₂.comap σ, S₂.comap σ⁆)
    (hs₁ : S₁ ≤ centralizer ({ū} : Set B))
    (hs₁s : (S₁.subgroupOf (centralizer ({ū} : Set B))).IsSubnormal)
    (hs₂ : S₂ ≤ centralizer ({ū} : Set B))
    (hs₂s : (S₂.subgroupOf (centralizer ({ū} : Set B))).IsSubnormal) :
    ∃ u : Q, orderOf u = 2 ∧ σ u = ū ∧
      ⁅S₁.comap σ, S₁.comap σ⁆ ≤ centralizer ({u} : Set Q) ∧
      IsPComponent 2 ((⁅S₁.comap σ, S₁.comap σ⁆).subgroupOf (centralizer ({u} : Set Q))) ∧
      ⁅S₂.comap σ, S₂.comap σ⁆ ≤ centralizer ({u} : Set Q) ∧
      IsPComponent 2 ((⁅S₂.comap σ, S₂.comap σ⁆).subgroupOf (centralizer ({u} : Set Q))) ∧
      Nonempty (↥⁅S₁.comap σ, S₁.comap σ⁆ ≃* SL(2, GaloisField p n)) ∧
      Nonempty (↥⁅S₂.comap σ, S₂.comap σ⁆ ≃* SL(2, GaloisField p n)) ∧
      ⁅⁅S₁.comap σ, S₁.comap σ⁆, ⁅S₂.comap σ, S₂.comap σ⁆⁆ = ⊥ ∧
      ⁅S₁.comap σ, S₁.comap σ⁆ ⊓ ⁅S₂.comap σ, S₂.comap σ⁆ = ⊥ ∧
      (center ↥(⁅S₁.comap σ, S₁.comap σ⁆ ⊔ ⁅S₂.comap σ, S₂.comap σ⁆)).map
          (⁅S₁.comap σ, S₁.comap σ⁆ ⊔ ⁅S₂.comap σ, S₂.comap σ⁆).subtype =
        zpowers u ⊔ zpowers c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at h5
    · exact h
  have h4 : 4 ≤ Nat.card (GaloisField p n) := by
    rw [GaloisField.card p n hn.ne']
    omega
  have hF : ringChar (GaloisField p n) ≠ 2 := by
    rw [ringChar.eq (GaloisField p n) p]
    exact hp2
  set T₁ := ⁅S₁.comap σ, S₁.comap σ⁆ with hT₁
  set T₂ := ⁅S₂.comap σ, S₂.comap σ⁆ with hT₂
  obtain ⟨hT₁S, hT₁inj⟩ := exists_sl_lift_of_split σ hker hker2 hS₁r hF h4 e₁
  obtain ⟨hT₂S, hT₂inj⟩ := exists_sl_lift_of_split σ hker hker2 hS₂r hF h4 e₂
  have hbij : ∀ {S : Subgroup B} {T' : Subgroup Q} (hTS : T'.map σ = S)
      (hinj : ∀ x ∈ T', σ x = 1 → x = 1) (hmem : ∀ x : T', σ x ∈ S),
      Function.Bijective ((σ.comp T'.subtype).codRestrict S hmem) := by
    intro S T' hTS hinj hmem
    refine ⟨fun x y hxy => ?_, ?_⟩
    · have h1 : σ ((x : Q) * (y : Q)⁻¹) = 1 := by
        rw [map_mul, map_inv, mul_inv_eq_one]
        exact congrArg Subtype.val hxy
      exact Subtype.ext (mul_inv_eq_one.mp (hinj _ (mul_mem x.2 (inv_mem y.2)) h1))
    · rintro ⟨s, hs⟩
      rw [← hTS] at hs
      obtain ⟨x, hx, rfl⟩ := hs
      exact ⟨⟨x, hx⟩, rfl⟩
  have hmem₁ : ∀ x : T₁, σ x ∈ S₁ := fun x => by rw [← hT₁S]; exact mem_map_of_mem σ x.2
  have hmem₂ : ∀ x : T₂, σ x ∈ S₂ := fun x => by rw [← hT₂S]; exact mem_map_of_mem σ x.2
  let f₁ : T₁ ≃* S₁ := MulEquiv.ofBijective _ (hbij hT₁S hT₁inj hmem₁)
  let f₂ : T₂ ≃* S₂ := MulEquiv.ofBijective _ (hbij hT₂S hT₂inj hmem₂)
  have hinj₁ : ∀ x ∈ T₁, ∀ y ∈ T₁, σ x = σ y → x = y := by
    intro x hx y hy h
    have h1 : σ (x * y⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hT₁inj _ (mul_mem hx (inv_mem hy)) h1)
  have hinj₂ : ∀ x ∈ T₂, ∀ y ∈ T₂, σ x = σ y → x = y := by
    intro x hx y hy h
    have h1 : σ (x * y⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hT₂inj _ (mul_mem hx (inv_mem hy)) h1)
  have hTp : ∀ {T : Subgroup Q} {S : Subgroup B}, Nonempty (T ≃* S) →
      Nonempty (S ≃* SL(2, GaloisField p n)) → ⁅T, T⁆ = T := by
    rintro T S ⟨f⟩ ⟨e⟩
    have hSL : Group.IsPerfect SL(2, GaloisField p n) :=
      CatalogueBGeneralLinear.specialLinear_perfect 2 _ le_rfl (Or.inr (by omega))
        (Or.inr (by omega))
    have : Group.IsPerfect T := Group.IsPerfect.ofSurjective (f := (f.trans e).symm.toMonoidHom)
      (f.trans e).symm.surjective
    exact Subgroup.isPerfect_iff.mp this
  have hT₁p := hTp ⟨f₁⟩ ⟨e₁⟩
  have hTT : ⁅T₁, T₂⁆ = ⊥ := by
    refine commutator_eq_bot_of_le_center hT₁p ?_
    rw [commutator_le]
    intro a ha b hb
    apply hker
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ (hmem₁ ⟨a, ha⟩) _ (hmem₂ ⟨b, hb⟩)
  have hTc : ∀ a ∈ T₁, ∀ b ∈ T₂, a * b = b * a := by
    intro a ha b hb
    have h1 := commutator_mem_commutator ha hb
    rw [hTT, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  obtain ⟨u₁, hu₁T, hu₁σ⟩ : ∃ u₁ ∈ T₁, σ u₁ = ū := by
    rw [← hT₁S] at hū₁
    exact hū₁
  obtain ⟨u₂, hu₂T, hu₂σ⟩ : ∃ u₂ ∈ T₂, σ u₂ = ū := by
    rw [← hT₂S] at hū₂
    exact hū₂
  have hū2 : ū * ū = 1 := by rw [← pow_two, ← hū, pow_orderOf_eq_one]
  have hu₁2 : u₁ * u₁ = 1 := hT₁inj _ (mul_mem hu₁T hu₁T) (by rw [map_mul, hu₁σ, hū2])
  have hu₁1 : u₁ ≠ 1 := by
    intro h
    have : ū = 1 := by rw [← hu₁σ, h, map_one]
    rw [this, orderOf_one] at hū
    exact absurd hū (by norm_num)
  have hu₁o : orderOf u₁ = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hu₁2) hu₁1
  have hfib : ∀ x ∈ T₁ ⊔ T₂, σ x = 1 → x = 1 ∨ x = u₁ * u₂ := by
    intro x hx hx1
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_commute hTc).mp hx
    rw [map_mul, mul_eq_one_iff_eq_inv] at hx1
    have hσa₁ : σ a ∈ S₁ := hmem₁ ⟨a, ha⟩
    have hσa₂ : σ a ∈ S₂ := by rw [hx1]; exact inv_mem (hmem₂ ⟨b, hb⟩)
    rcases hint _ hσa₁ hσa₂ with h | h
    · left
      have ha1 : a = 1 := hT₁inj a ha h
      have hb1 : b = 1 := hT₂inj b hb (by rw [h] at hx1; exact inv_eq_one.mp hx1.symm)
      rw [ha1, hb1, one_mul]
    · right
      have ha1 : a = u₁ := hinj₁ a ha u₁ hu₁T (by rw [h, hu₁σ])
      have hb1 : b = u₂ := hinj₂ b hb u₂ hu₂T (by
        rw [hu₂σ, ← inv_inv (σ b), ← hx1, h, inv_eq_of_mul_eq_one_right hū2])
      rw [ha1, hb1]
  have hcu : c = u₁ * u₂ := (hfib c hcT hc).resolve_left hc1
  have hu₁₂ : u₁ ≠ u₂ := by
    intro h
    apply hc1
    rw [hcu, ← h, hu₁2]
  have hinter : T₁ ⊓ T₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := mem_inf.mp hx
    rw [mem_bot]
    rcases hint _ (hmem₁ ⟨x, hx₁⟩) (hmem₂ ⟨x, hx₂⟩) with h | h
    · exact hT₁inj x hx₁ h
    · exfalso
      apply hu₁₂
      rw [← hinj₁ x hx₁ u₁ hu₁T (by rw [h, hu₁σ]), hinj₂ x hx₂ u₂ hu₂T (by rw [h, hu₂σ])]
  have hZS : ∀ {S : Subgroup B} (e : S ≃* SL(2, GaloisField p n)), ū ∈ S →
      (∀ y ∈ S, ū * y = y * ū) → ∀ y ∈ S, (∀ x ∈ S, y * x = x * y) → y = 1 ∨ y = ū := by
    intro S e hūS hūc y hy hyc
    obtain ⟨z, -, -, -, -, hz⟩ := exists_central_involution hp2 hn e
    rcases hz ū hūS hūc with h | h
    · exact absurd h (by intro h1; rw [h1, orderOf_one] at hū; exact absurd hū (by norm_num))
    · rw [h]
      exact hz y hy hyc
  have hūc₁ : ∀ y ∈ S₁, ū * y = y * ū := fun y hy => (hcomm y hy ū hū₂).symm
  have hūc₂ : ∀ y ∈ S₂, ū * y = y * ū := fun y hy => hcomm ū hū₁ y hy
  have hu₁c : ∀ x ∈ T₁, u₁ * x = x * u₁ := by
    intro x hx
    exact hinj₁ _ (mul_mem hu₁T hx) _ (mul_mem hx hu₁T) (by
      rw [map_mul, map_mul, hu₁σ]
      exact hūc₁ _ (hmem₁ ⟨x, hx⟩))
  have hu₂c : ∀ x ∈ T₂, u₂ * x = x * u₂ := by
    intro x hx
    exact hinj₂ _ (mul_mem hu₂T hx) _ (mul_mem hx hu₂T) (by
      rw [map_mul, map_mul, hu₂σ]
      exact hūc₂ _ (hmem₂ ⟨x, hx⟩))
  have hT₁C : T₁ ≤ centralizer ({u₁} : Set Q) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hu₁c x hx).symm
  have hT₂C : T₂ ≤ centralizer ({u₁} : Set Q) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hTc u₁ hu₁T x hx).symm
  have hCC : centralizer ({u₁} : Set Q) ≤ (centralizer ({ū} : Set B)).comap σ := by
    intro x hx
    rw [mem_comap, mem_centralizer_singleton_iff, ← hu₁σ, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp hx]
  have hsub₁ := isSubnormal_subgroupOf_of_le hCC (isSubnormal_commutator_comap σ hs₁ hs₁s)
  have hsub₂ := isSubnormal_subgroupOf_of_le hCC (isSubnormal_commutator_comap σ hs₂ hs₂s)
  refine ⟨u₁, hu₁o, hu₁σ, hT₁C, isPComponent_of_mulEquiv_sl hT₁C hsub₁ hp2 h5 (f₁.trans e₁),
    hT₂C, isPComponent_of_mulEquiv_sl hT₂C hsub₂ hp2 h5 (f₂.trans e₂), ⟨f₁.trans e₁⟩,
    ⟨f₂.trans e₂⟩, hTT, hinter, ?_⟩
  have hcZ : c ∈ center Q := hker (MonoidHom.mem_ker.mpr hc)
  apply le_antisymm
  · rintro _ ⟨⟨x, hx⟩, hxZ, rfl⟩
    change x ∈ zpowers u₁ ⊔ zpowers c
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_commute hTc).mp hx
    have hxc := mem_center_iff.mp hxZ
    have ha' : ∀ y ∈ T₁, a * y = y * a := by
      intro y hy
      have h1 := hxc ⟨y, mem_sup_left hy⟩
      have h2 : y * (a * b) = a * b * y := congrArg Subtype.val h1
      have h3 : b * y = y * b := (hTc y hy b hb).symm
      calc a * y = a * y * b * b⁻¹ := by group
        _ = a * (y * b) * b⁻¹ := by group
        _ = a * (b * y) * b⁻¹ := by rw [h3]
        _ = (a * b * y) * b⁻¹ := by group
        _ = (y * (a * b)) * b⁻¹ := by rw [h2]
        _ = y * a := by group
    have hb' : ∀ y ∈ T₂, b * y = y * b := by
      intro y hy
      have h1 := hxc ⟨y, mem_sup_right hy⟩
      have h2 : y * (a * b) = a * b * y := congrArg Subtype.val h1
      have h3 : a * y = y * a := hTc a ha y hy
      calc b * y = a⁻¹ * (a * b * y) := by group
        _ = a⁻¹ * (y * (a * b)) := by rw [h2]
        _ = a⁻¹ * (y * a) * b := by group
        _ = a⁻¹ * (a * y) * b := by rw [h3]
        _ = y * b := by group
    have hσa := hZS e₁ hū₁ hūc₁ (σ a) (hmem₁ ⟨a, ha⟩) (fun s hs => by
      rw [← hT₁S] at hs
      obtain ⟨y, hy, rfl⟩ := hs
      rw [← map_mul, ← map_mul, ha' y hy])
    have hσb := hZS e₂ hū₂ hūc₂ (σ b) (hmem₂ ⟨b, hb⟩) (fun s hs => by
      rw [← hT₂S] at hs
      obtain ⟨y, hy, rfl⟩ := hs
      rw [← map_mul, ← map_mul, hb' y hy])
    have hu₂ : u₂ = u₁ * c := by
      rw [hcu, ← mul_assoc, hu₁2, one_mul]
    have hmu₁ : u₁ ∈ zpowers u₁ ⊔ zpowers c := mem_sup_left (mem_zpowers u₁)
    have hmc : c ∈ zpowers u₁ ⊔ zpowers c := mem_sup_right (mem_zpowers c)
    have hma : a ∈ zpowers u₁ ⊔ zpowers c := by
      rcases hσa with h | h
      · rw [hT₁inj a ha h]
        exact one_mem _
      · rw [hinj₁ a ha u₁ hu₁T (by rw [h, hu₁σ])]
        exact hmu₁
    have hmb : b ∈ zpowers u₁ ⊔ zpowers c := by
      rcases hσb with h | h
      · rw [hT₂inj b hb h]
        exact one_mem _
      · rw [hinj₂ b hb u₂ hu₂T (by rw [h, hu₂σ]), hu₂]
        exact mul_mem hmu₁ hmc
    exact mul_mem hma hmb
  · refine sup_le ?_ ?_
    · rw [zpowers_le]
      refine ⟨⟨u₁, mem_sup_left hu₁T⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_center_iff]
      rintro ⟨y, hy⟩
      apply Subtype.ext
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_commute hTc).mp hy
      change a * b * u₁ = u₁ * (a * b)
      calc a * b * u₁ = a * (b * u₁) := by group
        _ = a * (u₁ * b) := by rw [hTc u₁ hu₁T b hb]
        _ = (a * u₁) * b := by group
        _ = (u₁ * a) * b := by rw [hu₁c a ha]
        _ = u₁ * (a * b) := by group
    · rw [zpowers_le]
      refine ⟨⟨c, hcT⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_center_iff]
      rintro ⟨y, hy⟩
      exact Subtype.ext (mem_center_iff.mp hcZ y)

end CFSG.ComponentClassification.Burgoyne.B
