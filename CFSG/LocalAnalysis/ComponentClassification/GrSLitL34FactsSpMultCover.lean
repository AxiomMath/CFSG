module

public import CFSG.Foundations.Basic
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.ComponentClassification.GSThmB.SpMult

open CFSG Subgroup CFSG.CosetTable
open scoped commutatorElement

@[expose] def sqCenter (Q : Type*) [Group Q] : Subgroup Q where
  carrier := {x | ∃ c ∈ center Q, c ^ 2 = x}
  mul_mem' := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    refine ⟨c * d, mul_mem hc hd, ?_⟩
    exact Commute.mul_pow (mem_center_iff.mp hd c) 2
  one_mem' := ⟨1, one_mem _, one_pow 2⟩
  inv_mem' := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c⁻¹, inv_mem hc, inv_pow c 2⟩

theorem sqCenter_le_center (Q : Type*) [Group Q] : sqCenter Q ≤ center Q := by
  rintro _ ⟨c, hc, rfl⟩
  exact pow_mem hc 2

instance sqCenter_normal (Q : Type*) [Group Q] : (sqCenter Q).Normal :=
  ⟨fun n hn g => by
    rw [mem_center_iff.mp (sqCenter_le_center Q hn) g, mul_inv_cancel_right]
    exact hn⟩

theorem odd_card_center_of_card_le {G : Type} [Group G] [Finite G]
    (hbound : ∀ (E : Type) [Group E] [Finite E] (ρ : E →* G), Function.Surjective ρ →
      ρ.ker ≤ center E → (∀ v ∈ ρ.ker, v * v = 1) → Group.IsPerfect E →
        Nat.card E ≤ Nat.card G)
    (Q : Type) [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    (he : Nonempty (Q ⧸ center Q ≃* G)) : Odd (Nat.card (center Q)) := by
  obtain ⟨e⟩ := he
  have : Group.IsPerfect Q := hQ.1
  set S := sqCenter Q with hS
  have hSC : S ≤ center Q := sqCenter_le_center Q
  set π : Q →* G := e.toMonoidHom.comp (QuotientGroup.mk' (center Q)) with hπ
  have hπ1 : ∀ q : Q, π q = 1 ↔ q ∈ center Q := fun q => by
    simp only [hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]
  have hSπ : S ≤ π.ker := fun x hx => (hπ1 x).2 (hSC hx)
  set ρ : Q ⧸ S →* G := QuotientGroup.lift S π hSπ with hρdef
  have hρmk : ∀ q : Q, ρ (q : Q ⧸ S) = π q := fun q => rfl
  have hρ : Function.Surjective ρ := by
    intro g
    obtain ⟨x, rfl⟩ := e.surjective g
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨(q : Q ⧸ S), rfl⟩
  have hker : ρ.ker ≤ center (Q ⧸ S) := by
    intro v hv
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective v
    have hq : q ∈ center Q := (hπ1 q).1 hv
    rw [mem_center_iff]
    intro w
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hq p]
  have hexp : ∀ v ∈ ρ.ker, v * v = 1 := by
    intro v hv
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective v
    have hq : q ∈ center Q := (hπ1 q).1 hv
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact ⟨q, hq, by rw [sq]⟩
  have hle := hbound (Q ⧸ S) ρ hρ hker hexp inferInstance
  have hcard : Nat.card (Q ⧸ S) = Nat.card G * Nat.card ρ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).toEquiv]
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hk : Nat.card ρ.ker = 1 := by
    have h1 : 0 < Nat.card ρ.ker := Nat.card_pos
    rw [hcard] at hle
    have : Nat.card G * Nat.card ρ.ker ≤ Nat.card G * 1 := by rw [mul_one]; exact hle
    have := Nat.le_of_mul_le_mul_left this hpos
    omega
  have hCS : ∀ c ∈ center Q, c ∈ S := fun c hc => by
    have h1 : (c : Q ⧸ S) ∈ ρ.ker := (hπ1 c).2 hc
    rw [Subgroup.eq_bot_of_card_eq ρ.ker hk, mem_bot, QuotientGroup.eq_one_iff] at h1
    exact h1
  by_contra hodd
  have h2 : 2 ∣ Nat.card (center Q) := (Nat.not_odd_iff_even.mp hodd).two_dvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := center Q) 2 h2
  let sqf : center Q → center Q := fun x => x ^ 2
  have hsurj : Function.Surjective sqf := by
    intro x
    obtain ⟨d, hd, hdx⟩ := hCS x x.2
    exact ⟨⟨d, hd⟩, Subtype.ext hdx⟩
  have hinj : Function.Injective sqf := Finite.injective_iff_surjective.mpr hsurj
  have hc1 : c = 1 := hinj (by
    change c ^ 2 = 1 ^ 2
    rw [one_pow, ← hc, pow_orderOf_eq_one])
  rw [hc1, orderOf_one] at hc
  exact absurd hc (by norm_num)

theorem mul_self_eq_one_of_lift {E G : Type*} [Group E] [Group G] {ρ : E →* G}
    (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ center E) (hexp : ∀ v ∈ ρ.ker, v * v = 1)
    {t₀ : G} {b₀ : E} (hb₀ : ρ b₀ = t₀) (hb₀2 : b₀ * b₀ = 1)
    (hcl : ∀ t : G, orderOf t = 2 → ∃ g : G, g * t₀ * g⁻¹ = t) {w : E}
    (hw : ρ w * ρ w = 1) : w * w = 1 := by
  by_cases h1 : ρ w = 1
  · exact hexp w h1
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have ho : orderOf (ρ w) = 2 := orderOf_eq_prime (by rw [sq, hw]) h1
    obtain ⟨g, hg⟩ := hcl _ ho
    obtain ⟨k, rfl⟩ := hρ g
    have hu2 : k * b₀ * k⁻¹ * (k * b₀ * k⁻¹) = 1 := by
      calc k * b₀ * k⁻¹ * (k * b₀ * k⁻¹) = k * (b₀ * b₀) * k⁻¹ := by group
        _ = 1 := by rw [hb₀2, mul_one, mul_inv_cancel]
    have hv : (k * b₀ * k⁻¹)⁻¹ * w ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hb₀, hg,
        inv_mul_cancel]
    have hvc := mem_center_iff.mp (hker hv)
    set u := k * b₀ * k⁻¹
    set v := u⁻¹ * w
    have hw' : w = u * v := by simp [v]
    rw [hw']
    calc u * v * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [hvc u]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [hu2, hexp v hv, one_mul]

theorem commutatorElement_mul_central {E : Type*} [Group E] {x y z z' : E}
    (hz : z ∈ center E) (hz' : z' ∈ center E) : ⁅x * z, y * z'⁆ = ⁅x, y⁆ := by
  have h1 := mem_center_iff.mp hz
  have h2 := mem_center_iff.mp hz'
  simp only [commutatorElement_def, mul_inv_rev]
  calc x * z * (y * z') * (z⁻¹ * x⁻¹) * (z'⁻¹ * y⁻¹) =
      x * (z * y) * (z' * z⁻¹) * x⁻¹ * z'⁻¹ * y⁻¹ := by group
    _ = x * (y * z) * (z⁻¹ * z') * x⁻¹ * z'⁻¹ * y⁻¹ := by
      rw [h1 y, ← h2 z⁻¹]
    _ = x * y * (z' * x⁻¹) * z'⁻¹ * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [← h2 x⁻¹]; group

theorem eq_top_of_sup_center {E : Type*} [Group E] [hperf : Group.IsPerfect E]
    {H Z : Subgroup E} (hZ : Z ≤ center E) (hHZ : H ⊔ Z = ⊤) : H = ⊤ := by
  have : Z.Normal := ⟨fun n hn g => by
    rw [mem_center_iff.mp (hZ hn) g, mul_inv_cancel_right]
    exact hn⟩
  have hmem : ∀ x : E, ∃ h ∈ H, ∃ z ∈ Z, h * z = x := by
    intro x
    have hx : x ∈ ((H ⊔ Z : Subgroup E) : Set E) := by rw [hHZ]; exact mem_top x
    rw [Subgroup.mul_normal] at hx
    obtain ⟨h, hh, z, hz, rfl⟩ := hx
    exact ⟨h, hh, z, hz, rfl⟩
  rw [eq_top_iff, ← hperf.commutator_eq_top, commutator_def, Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨h, hh, z, hz, rfl⟩ := hmem x
  obtain ⟨h', hh', z', hz', rfl⟩ := hmem y
  rw [commutatorElement_mul_central (hZ hz) (hZ hz'), commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hh hh') (inv_mem hh)) (inv_mem hh')

theorem card_le_card_of_relators {E G : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    [Group G] {m : ℕ} {ws : List (List (Fin m × Bool))} [Finite (PG m ws)] (ρ : E →* G)
    (hker : ρ.ker ≤ center E) (f : Fin m → E)
    (hrel : ∀ w ∈ ws, FreeGroup.lift f (FreeGroup.mk w) = 1)
    (hgen : (closure (Set.range f) ⊔ ρ.ker : Subgroup E) = ⊤) :
    Nat.card E ≤ Nat.card (PG m ws) := by
  have hrel' : ∀ r ∈ {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk},
      FreeGroup.lift f r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact hrel w hw
  set φ : PG m ws →* E := PresentedGroup.toGroup hrel' with hφ
  have hrange : φ.range = ⊤ := by
    refine eq_top_of_sup_center hker (eq_top_iff.mpr ?_)
    rw [← hgen]
    refine sup_le_sup_right ?_ _
    rw [closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of hrel'⟩
  exact Nat.card_le_card_of_surjective φ (MonoidHom.range_eq_top.mp hrange)

end CFSG.ComponentClassification.GSThmB.SpMult
