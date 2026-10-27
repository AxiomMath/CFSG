module

public import CFSG.GH74.QTGen4.Recog.Ku.CloseCent
public import CFSG.GH74.QTGen4.Recog.Ku.CloseFinB
public import CFSG.GH74.QTGen4.Recog.Ku.CloseFinC

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Quasithin.HSType

variable {G : Type} [Group G]

theorem mem_sup_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : G}
    (hg : g ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  let S : Subgroup G :=
    { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
        simp only [mul_assoc]
        congr 1
        rw [← mul_assoc, (h a₂ ha₂ b₁ hb₁).symm, mul_assoc]
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        rw [mul_inv_rev]
        exact ((Commute.inv_inv (h a ha b hb : Commute a b)).eq).symm }
  have hle : A ⊔ B ≤ S :=
    sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩)
      (fun b hb => ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩)
  exact hle hg

theorem card_sup_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAB : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  let f : A × B → ↥(A ⊔ B) := fun p =>
    ⟨p.1.1 * p.2.1, mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hbij : Function.Bijective f := by
    refine ⟨fun p q hpq => ?_, fun y => ?_⟩
    · have hab : p.1.1 * p.2.1 = q.1.1 * q.2.1 := congrArg Subtype.val hpq
      have hA : q.1.1⁻¹ * p.1.1 ∈ A := A.mul_mem (A.inv_mem q.1.2) p.1.2
      have hB : q.2.1 * p.2.1⁻¹ ∈ B := B.mul_mem q.2.2 (B.inv_mem p.2.2)
      have hEq : q.1.1⁻¹ * p.1.1 = q.2.1 * p.2.1⁻¹ := by
        have := congrArg (fun t => q.1.1⁻¹ * t * p.2.1⁻¹) hab
        simpa [mul_assoc] using this
      have hmem : q.1.1⁻¹ * p.1.1 ∈ A ⊓ B :=
        Subgroup.mem_inf.mpr ⟨hA, by rw [hEq]; exact hB⟩
      rw [hAB, Subgroup.mem_bot] at hmem
      have hpa : p.1.1 = q.1.1 := (inv_mul_eq_one.mp hmem).symm
      have hpb : p.2.1 = q.2.1 := by
        rw [hpa] at hab
        exact mul_left_cancel hab
      exact Prod.ext (Subtype.ext hpa) (Subtype.ext hpb)
    · obtain ⟨a, ha, b, hb, hy⟩ := mem_sup_of_commute h y.2
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hy.symm⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hbij)).symm

namespace KuA6Model

variable [Finite G] {E W V2 N : Subgroup G} {z : G} (Ψ : KuA6Model E W V2 N z)
include Ψ

theorem perm_order_three {x : G} (hHN : Subgroup.centralizer ({z} : Set G) ≤ N)
    (hxH : x ∈ Subgroup.centralizer ({z} : Set G)) (hx : orderOf x = 3) :
    Equiv.Perm.sign (Ψ.π ⟨x, hHN hxH⟩) = 1 ∧ Ψ.π ⟨x, hHN hxH⟩ ^ 3 = 1 ∧
      Ψ.π ⟨x, hHN hxH⟩ ≠ 1 ∧ actS6 (Ψ.π ⟨x, hHN hxH⟩) (spE 0) = spE 0 ∧
      ∀ v : SpV, x * Ψ.Φ v = Ψ.Φ v * x ↔ actS6 (Ψ.π ⟨x, hHN hxH⟩) v = v := by
  have hN : x ∈ N := hHN hxH
  have hzx : z * x = x * z := Subgroup.mem_centralizer_iff.mp hxH z (Set.mem_singleton z)
  have hact : ∀ v : SpV, x * Ψ.Φ v * x⁻¹ = Ψ.Φ (actS6 (Ψ.π ⟨x, hN⟩) v) :=
    fun v => Ψ.act ⟨x, hN⟩ v
  have h3 : (⟨x, hN⟩ : ↥N) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hx]
    exact pow_orderOf_eq_one x
  have hpow : Ψ.π ⟨x, hN⟩ ^ 3 = 1 := by
    rw [← map_pow, h3, map_one]
  have hne : Ψ.π ⟨x, hN⟩ ≠ 1 := by
    intro h1
    have hxE : x ∈ E := (Ψ.ker ⟨x, hN⟩).mp h1
    have hsq : x * x = 1 := Ψ.E_mul_self x hxE
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    rw [hx] at h2
    norm_num at h2
  have hfix : actS6 (Ψ.π ⟨x, hN⟩) (spE 0) = spE 0 := by
    have h1 : x * z * x⁻¹ = z := by rw [← hzx, mul_inv_cancel_right]
    have h2 : Ψ.Φ (actS6 (Ψ.π ⟨x, hN⟩) (spE 0)) = Ψ.Φ (spE 0) := by
      rw [← hact (spE 0), Ψ.e0, h1]
    exact Ψ.inj h2
  refine ⟨Equiv.Perm.mem_alternatingGroup.mp (Ψ.π_alt _), hpow, hne, hfix, fun v => ?_⟩
  constructor
  · intro hc
    apply Ψ.inj
    rw [← hact v]
    exact mul_inv_eq_iff_eq_mul.mpr hc
  · intro h
    have hv := hact v
    rw [h] at hv
    exact mul_inv_eq_iff_eq_mul.mp hv

theorem card_delta (hHN : Subgroup.centralizer ({z} : Set G) ≤ N) {x : G}
    (hxH : x ∈ Subgroup.centralizer ({z} : Set G)) (hx : orderOf x = 3) :
    Nat.card (kuDelta E x) = 4 := by
  obtain ⟨hsgn, hpow, hne, hfix, hcomm⟩ := Ψ.perm_order_three hHN hxH hx
  have hF := card_fix_order_three _ hsgn hpow hne hfix
  have hmem : ∀ v : SpV, actS6 (Ψ.π ⟨x, hHN hxH⟩) v = v → Ψ.Φ v ∈ kuDelta E x := by
    intro v hv
    refine Subgroup.mem_inf.mpr ⟨Ψ.mem v, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (hcomm v).mpr hv
  have hbij : Function.Bijective (fun v : {v : SpV // actS6 (Ψ.π ⟨x, hHN hxH⟩) v = v} =>
      (⟨Ψ.Φ v.1, hmem v.1 v.2⟩ : kuDelta E x)) := by
    refine ⟨fun a b hab => Subtype.ext (Ψ.inj (congrArg Subtype.val hab)), fun y => ?_⟩
    obtain ⟨v, hv⟩ := Ψ.surj y.1 (Subgroup.mem_inf.mp y.2).1
    have hc : x * y.1 = y.1 * x :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp y.2).2 x (Set.mem_singleton x)
    rw [← hv] at hc
    exact ⟨⟨v, (hcomm v).mp hc⟩, Subtype.ext hv⟩
  have hcard : Nat.card (kuDelta E x) =
      Nat.card {v : SpV // actS6 (Ψ.π ⟨x, hHN hxH⟩) v = v} :=
    (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_subtype, hF]

theorem no_invert_centralize_delta (hHN : Subgroup.centralizer ({z} : Set G) ≤ N) {x : G}
    (hxH : x ∈ Subgroup.centralizer ({z} : Set G)) (hx : orderOf x = 3) {d : G}
    (hdx : d * x * d⁻¹ = x⁻¹) (hdΔ : ∀ e ∈ kuDelta E x, d * e * d⁻¹ = e) : False := by
  have hN : x ∈ N := hHN hxH
  have hzx : z * x = x * z := Subgroup.mem_centralizer_iff.mp hxH z (Set.mem_singleton z)
  have hzΔ : z ∈ kuDelta E x := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have := Ψ.mem (spE 0)
      rwa [Ψ.e0] at this
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hzx.symm
  have hdz : d * z * d⁻¹ = z := hdΔ z hzΔ
  have hdH : d ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (mul_inv_eq_iff_eq_mul.mp hdz).symm
  have hdN : d ∈ N := hHN hdH
  obtain ⟨hsgn, hpow, hne, hfix, _⟩ := Ψ.perm_order_three hHN hxH hx
  have key : (⟨d, hdN⟩ : ↥N) * ⟨x, hN⟩ * (⟨d, hdN⟩)⁻¹ = (⟨x, hN⟩ : ↥N)⁻¹ :=
    Subtype.ext (by simpa using hdx)
  have hconj := congrArg Ψ.π key
  rw [map_mul, map_mul, map_inv, map_inv] at hconj
  have hσ : Equiv.Perm.sign (Ψ.π ⟨d, hdN⟩) = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp (Ψ.π_alt _)
  obtain ⟨v, hτv, hσv⟩ :=
    no_invert_fixing (Ψ.π ⟨x, hN⟩) hsgn hpow hne hfix (Ψ.π ⟨d, hdN⟩) hσ hconj
  have hΔv : Ψ.Φ v ∈ kuDelta E x := by
    refine Subgroup.mem_inf.mpr ⟨Ψ.mem v, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact ((Ψ.perm_order_three hHN hxH hx).2.2.2.2 v).mpr hτv
  have hdv : d * Ψ.Φ v * d⁻¹ = Ψ.Φ v := hdΔ _ hΔv
  have hact : d * Ψ.Φ v * d⁻¹ = Ψ.Φ (actS6 (Ψ.π ⟨d, hdN⟩) v) := Ψ.act ⟨d, hdN⟩ v
  exact hσv (Ψ.inj (hact.symm.trans hdv))

theorem perm_fix_e0 {x : G} (hHN : Subgroup.centralizer ({z} : Set G) ≤ N)
    (hxH : x ∈ Subgroup.centralizer ({z} : Set G)) :
    actS6 (Ψ.π ⟨x, hHN hxH⟩) (spE 0) = spE 0 := by
  have hN : x ∈ N := hHN hxH
  have hzx : z * x = x * z := Subgroup.mem_centralizer_iff.mp hxH z (Set.mem_singleton z)
  have h1 : x * z * x⁻¹ = z := by rw [← hzx, mul_inv_cancel_right]
  have h2 : Ψ.Φ (actS6 (Ψ.π ⟨x, hN⟩) (spE 0)) = Ψ.Φ (spE 0) := by
    rw [← Ψ.act ⟨x, hN⟩ (spE 0), Ψ.e0, h1]
  exact Ψ.inj h2

theorem centralizer_inf_eq (hHN : Subgroup.centralizer ({z} : Set G) ≤ N) {x : G}
    (hxH : x ∈ Subgroup.centralizer ({z} : Set G)) (hx : orderOf x = 3) :
    Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) =
      Subgroup.zpowers x ⊔ kuDelta E x := by
  have hN : x ∈ N := hHN hxH
  obtain ⟨hsgn, hpow, hne, hfix, _⟩ := Ψ.perm_order_three hHN hxH hx
  set τ : Equiv.Perm (Fin 6) := Ψ.π ⟨x, hN⟩ with hτ
  have hS3 := card_centralizer_stab_order_three τ hsgn hpow hne hfix
  have hTτ : τ * (τ * τ) = 1 := by rw [← pow_three]; exact hpow
  have hT3 : ({1, τ, τ * τ} : Finset (Equiv.Perm (Fin 6))).card = 3 := by
    apply Finset.card_eq_three.mpr
    refine ⟨1, τ, τ * τ, Ne.symm hne, ?_, ?_, rfl⟩
    · intro h
      rw [← h, mul_one] at hTτ
      exact hne hTτ
    · intro h
      have h' : τ * 1 = τ * τ := by rw [mul_one]; exact h
      exact hne (mul_left_cancel h').symm
  have hTS : ({1, τ, τ * τ} : Finset (Equiv.Perm (Fin 6))) ⊆
      Finset.univ.filter fun σ : Equiv.Perm (Fin 6) =>
        Equiv.Perm.sign σ = 1 ∧ actS6 σ (spE 0) = spE 0 ∧ σ * τ = τ * σ := by
    intro σ hσ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hσ with rfl | rfl | rfl
    · exact ⟨map_one _, by rw [actS6_one], by rw [one_mul, mul_one]⟩
    · exact ⟨hsgn, hfix, rfl⟩
    · refine ⟨by rw [map_mul, hsgn, mul_one], ?_, mul_assoc _ _ _⟩
      rw [actS6_mul, hfix, hfix]
  have hTeq := Finset.eq_of_subset_of_card_le hTS (le_of_eq (by rw [hS3, hT3]))
  apply le_antisymm
  · intro y hy
    obtain ⟨hyH, hyC⟩ := Subgroup.mem_inf.mp hy
    have hyN : y ∈ N := hHN hyH
    have hyx : x * y = y * x := Subgroup.mem_centralizer_iff.mp hyC x (Set.mem_singleton x)
    have hσS : Ψ.π ⟨y, hyN⟩ ∈ Finset.univ.filter fun σ : Equiv.Perm (Fin 6) =>
        Equiv.Perm.sign σ = 1 ∧ actS6 σ (spE 0) = spE 0 ∧ σ * τ = τ * σ := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ⟨Equiv.Perm.mem_alternatingGroup.mp (Ψ.π_alt _),
        Ψ.perm_fix_e0 hHN hyH, ?_⟩⟩
      rw [hτ, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (by simp only [Subgroup.coe_mul]; exact hyx.symm)
    have hσT : Ψ.π ⟨y, hyN⟩ ∈ ({1, τ, τ * τ} : Finset (Equiv.Perm (Fin 6))) := by
      rw [hTeq]
      exact hσS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσT
    rcases hσT with h1 | h1 | h1
    · have hyE : y ∈ E := (Ψ.ker ⟨y, hyN⟩).mp h1
      exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hyE, hyC⟩)
    · have hgN : x⁻¹ * y ∈ N := mul_mem (inv_mem hN) hyN
      have hsplit : Ψ.π ⟨x⁻¹ * y, hgN⟩ = τ⁻¹ * Ψ.π ⟨y, hyN⟩ := by
        rw [hτ, ← map_inv, ← map_mul]
        congr 1
      have hgE : x⁻¹ * y ∈ E := (Ψ.ker ⟨x⁻¹ * y, hgN⟩).mp (by rw [hsplit, h1, inv_mul_cancel])
      have hgC : x⁻¹ * y ∈ Subgroup.centralizer ({x} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh, ← mul_assoc, mul_inv_cancel, one_mul, mul_assoc, ← hyx, inv_mul_cancel_left]
      have hmem : x * (x⁻¹ * y) ∈ Subgroup.zpowers x ⊔ kuDelta E x :=
        mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
          (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hgE, hgC⟩))
      rwa [mul_inv_cancel_left] at hmem
    · have hgN : y * x ∈ N := mul_mem hyN hN
      have hsplit : Ψ.π ⟨y * x, hgN⟩ = Ψ.π ⟨y, hyN⟩ * τ := by
        rw [hτ, ← map_mul]
        congr 1
      have hgE : y * x ∈ E := (Ψ.ker ⟨y * x, hgN⟩).mp (by rw [hsplit, h1, mul_assoc]; exact hTτ)
      have hgC : y * x ∈ Subgroup.centralizer ({x} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh, ← mul_assoc, hyx]
      have hmem : x⁻¹ * (y * x) ∈ Subgroup.zpowers x ⊔ kuDelta E x :=
        mul_mem (Subgroup.mem_sup_left (inv_mem (Subgroup.mem_zpowers x)))
          (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hgE, hgC⟩))
      rwa [← hyx, inv_mul_cancel_left] at hmem
  · refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      refine Subgroup.mem_inf.mpr ⟨hxH, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
    · intro e he
      obtain ⟨heE, heC⟩ := Subgroup.mem_inf.mp he
      exact Subgroup.mem_inf.mpr ⟨Ψ.E_le_centralizer_z heE, heC⟩

theorem card_centralizer_inf (hHN : Subgroup.centralizer ({z} : Set G) ≤ N) {x : G}
    (hxH : x ∈ Subgroup.centralizer ({z} : Set G)) (hx : orderOf x = 3) :
    Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) = 12 := by
  rw [Ψ.centralizer_inf_eq hHN hxH hx]
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ d ∈ kuDelta E x, a * d = d * a := by
    intro a ha d hd
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hxd : Commute x d :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).2 x (Set.mem_singleton x)
    exact (hxd.zpow_left k).eq
  have hdisj : Subgroup.zpowers x ⊓ kuDelta E x = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgz, hgd⟩ := Subgroup.mem_inf.mp hg
    have hg2 : g * g = 1 := Ψ.E_mul_self g (Subgroup.mem_inf.mp hgd).1
    have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg2)
    have h3 : orderOf g ∣ 3 := by
      have := orderOf_dvd_of_mem_zpowers hgz
      rwa [hx] at this
    have h1 : orderOf g = 1 := by
      have hgcd := Nat.dvd_gcd h3 h2
      have h4 : Nat.gcd 3 2 = 1 := by norm_num
      rw [h4] at hgcd
      exact Nat.dvd_one.mp hgcd
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)
  rw [card_sup_of_commute hcomm hdisj, Nat.card_zpowers, hx, Ψ.card_delta hHN hxH hx]

theorem card_centralizer_delta (hHN : Subgroup.centralizer ({z} : Set G) ≤ N) {x : G}
    (hxH : x ∈ Subgroup.centralizer ({z} : Set G)) (hx : orderOf x = 3) {i : G}
    (hi : i ∈ kuDelta E x) (hi1 : i ≠ 1) :
    Nat.card ↥(Subgroup.centralizer ({i} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) = 12 := by
  obtain ⟨g, hg⟩ := Ψ.exists_conj_z (Subgroup.mem_inf.mp hi).1 hi1
  have hcx : x * i = i * x :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hi).2 x (Set.mem_singleton x)
  have hC : ∀ (c y : G), y ∈ Subgroup.centralizer ({c} : Set G) ↔ c * y = y * c :=
    fun c y => by rw [Subgroup.mem_centralizer_iff]; simp
  have hkey : ∀ a b : G, a * b = b * a ↔
      (MulAut.conj g⁻¹) a * (MulAut.conj g⁻¹) b = (MulAut.conj g⁻¹) b * (MulAut.conj g⁻¹) a :=
    fun a b => by
      rw [← map_mul, ← map_mul]
      exact (MulAut.conj g⁻¹).injective.eq_iff.symm
  have hz : (MulAut.conj g⁻¹) i = z := by
    rw [← hg, MulAut.conj_apply]
    group
  have hconjx : MulAut.conj g ((MulAut.conj g⁻¹) x) = x := by
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  have hzx' : z * (MulAut.conj g⁻¹) x = (MulAut.conj g⁻¹) x * z := by
    apply (MulAut.conj g).injective
    rw [map_mul, map_mul, hconjx, MulAut.conj_apply, hg]
    exact hcx.symm
  have hzH : (MulAut.conj g⁻¹) x ∈ Subgroup.centralizer ({z} : Set G) :=
    (hC z _).mpr hzx'
  have hord : orderOf ((MulAut.conj g⁻¹) x) = 3 :=
    (orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective x).trans hx
  have hiff : ∀ y : G, y ∈ Subgroup.centralizer ({i} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)
      ↔ (MulAut.conj g⁻¹) y ∈ Subgroup.centralizer ({z} : Set G) ⊓
          Subgroup.centralizer ({(MulAut.conj g⁻¹) x} : Set G) := by
    intro y
    simp only [Subgroup.mem_inf, hC]
    constructor
    · rintro ⟨h1, h2⟩
      have A1 := (hkey y i).mp h1.symm
      rw [hz] at A1
      have A2 := ((hkey y x).mp h2.symm).symm
      exact ⟨A1.symm, A2⟩
    · rintro ⟨h1, h2⟩
      have B1 : (MulAut.conj g⁻¹) y * (MulAut.conj g⁻¹) i = (MulAut.conj g⁻¹) i * (MulAut.conj g⁻¹) y := by
        rw [hz]
        exact h1.symm
      have B2 : (MulAut.conj g⁻¹) y * (MulAut.conj g⁻¹) x = (MulAut.conj g⁻¹) x * (MulAut.conj g⁻¹) y :=
        h2.symm
      exact ⟨((hkey y i).mpr B1).symm, ((hkey y x).mpr B2).symm⟩
  rw [Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj g⁻¹).toEquiv hiff)]
  exact Ψ.card_centralizer_inf hHN hzH hord

end KuA6Model

end CFSG.GH74.QTGen4.Ku
