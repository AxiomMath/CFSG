module

public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup

variable {G : Type*} [Group G]

section Conj

variable {X : Subgroup G} {t : G}

theorem conj_mem_D4 (htX : t ∈ normalizer (X : Set G)) (ht : t * t = 1) {x : G}
    (hx : x ∈ X) : t * x * t ∈ X := by
  have h := (mem_normalizer_iff.1 htX x).1 hx
  rwa [inv_eq_of_mul_eq_one_right ht] at h

theorem conj_mem_center_D4 (htX : t ∈ normalizer (X : Set G)) (ht : t * t = 1) {z : G}
    (hz : z ∈ X ⊓ centralizer (X : Set G)) : t * z * t ∈ X ⊓ centralizer (X : Set G) := by
  refine ⟨conj_mem_D4 htX ht hz.1, mem_centralizer_iff.2 fun x hx => ?_⟩
  have hx' : t * x * t ∈ X := conj_mem_D4 htX ht hx
  have hc := mem_centralizer_iff.1 hz.2 _ hx'
  calc x * (t * z * t) = t * ((t * x * t) * z) * t := by
        rw [show t * ((t * x * t) * z) * t = (t * t) * x * (t * z * t) by group, ht, one_mul]
    _ = t * (z * (t * x * t)) * t := by rw [hc]
    _ = t * z * t * x := by
        rw [show t * (z * (t * x * t)) * t = t * z * t * x * (t * t) by group, ht, mul_one]

theorem center_comm_D4 {z x : G} (hz : z ∈ X ⊓ centralizer (X : Set G)) (hx : x ∈ X) :
    z * x = x * z :=
  (mem_centralizer_iff.1 hz.2 x hx).symm

end Conj

section Norm

variable [Finite G] {X : Subgroup G} {t : G}

theorem exists_mul_conj_of_mem_center_D4 (ht : t * t = 1) (htX : t ∈ normalizer (X : Set G))
    (hZ : ∀ z ∈ X ⊓ centralizer (X : Set G), z * z = 1)
    (hcardZ : Nat.card (X ⊓ centralizer (X : Set G) : Subgroup G) =
      Nat.card (X ⊓ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2)
    {v : G} (hv : v ∈ X ⊓ centralizer (X : Set G) ⊓ centralizer ({t} : Set G)) :
    ∃ w ∈ X ⊓ centralizer (X : Set G), v = w * (t * w * t) := by
  classical
  set Z := X ⊓ centralizer (X : Set G) with hZdef
  have hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb => center_comm_D4 ha hb.1
  have hconj : ∀ z ∈ Z, t * z * t ∈ Z := fun z hz => conj_mem_center_D4 htX ht hz
  let N : Z →* Z :=
    { toFun := fun z => ⟨z * (t * z * t), mul_mem z.2 (hconj z z.2)⟩
      map_one' := Subtype.ext (by simp [ht])
      map_mul' := fun a b => Subtype.ext (by
        change (a : G) * b * (t * (a * b) * t) = a * (t * a * t) * (b * (t * b * t))
        have e : t * ((a : G) * b) * t = (t * a * t) * (t * b * t) := by
          rw [show (t * a * t) * (t * b * t) = t * a * (t * t) * b * t by group, ht, mul_one]
          group
        rw [e]
        have h1 := hZc _ (hconj a a.2) _ b.2
        calc (a : G) * b * ((t * a * t) * (t * b * t)) = a * (b * (t * a * t)) * (t * b * t) := by
              group
          _ = a * ((t * a * t) * b) * (t * b * t) := by rw [h1]
          _ = a * (t * a * t) * (b * (t * b * t)) := by group) }
  have hN : ∀ z : Z, (N z : G) = z * (t * z * t) := fun _ => rfl
  have hker : N.ker.map Z.subtype = Z ⊓ centralizer ({t} : Set G) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have h1 : (z : G) * (t * z * t) = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.1 hz)
        rw [hN, Subgroup.coe_one] at this
        exact this
      have h2 : t * z * t = z := by
        have h3 := eq_inv_of_mul_eq_one_right h1
        rwa [inv_eq_of_mul_eq_one_right (hZ z z.2)] at h3
      refine ⟨z.2, mem_centralizer_singleton_iff.2 ?_⟩
      calc (z : G) * t = t * z * t * t := by rw [h2]
        _ = t * z := by rw [mul_assoc, ht, mul_one]
    · rintro ⟨hxZ, hxt⟩
      refine ⟨⟨x, hxZ⟩, MonoidHom.mem_ker.2 (Subtype.ext ?_), rfl⟩
      have hxt' : x * t = t * x := mem_centralizer_singleton_iff.1 hxt
      change x * (t * x * t) = 1
      rw [← hxt', mul_assoc, ht, mul_one]
      exact hZ x hxZ
  have hrange : N.range.map Z.subtype ≤ Z ⊓ centralizer ({t} : Set G) := by
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨(N z).2, mem_centralizer_singleton_iff.2 ?_⟩
    change (z : G) * (t * z * t) * t = t * (z * (t * z * t))
    have h1 := hZc _ z.2 _ (hconj z z.2)
    calc (z : G) * (t * z * t) * t = z * t * z * (t * t) := by group
      _ = (t * t) * z * t * z := by rw [ht, mul_one, one_mul]
      _ = t * ((t * z * t) * z) := by group
      _ = t * (z * (t * z * t)) := by rw [← h1]
  have hcard := Subgroup.card_ker_mul_card_range N
  rw [← card_map_of_injective (K := N.ker) Z.subtype_injective, hker,
    ← card_map_of_injective (K := N.range) Z.subtype_injective] at hcard
  have hcZ : Nat.card Z = Nat.card ↥(Z ⊓ centralizer ({t} : Set G)) ^ 2 := hcardZ
  rw [hcZ, sq] at hcard
  have hpos : 0 < Nat.card ↥(Z ⊓ centralizer ({t} : Set G)) := Nat.card_pos
  have heq := Nat.eq_of_mul_eq_mul_left hpos hcard
  have hle := eq_of_le_of_card_ge hrange heq.symm.le
  rw [← hle] at hv
  obtain ⟨_, ⟨z, rfl⟩, rfl⟩ := hv
  exact ⟨z, z.2, rfl⟩

theorem exists_mul_of_conj_mem_center_D4 (ht : t * t = 1) (htX : t ∈ normalizer (X : Set G))
    (hZ : ∀ z ∈ X ⊓ centralizer (X : Set G), z * z = 1)
    (hcardZ : Nat.card (X ⊓ centralizer (X : Set G) : Subgroup G) =
      Nat.card (X ⊓ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2)
    {b : G} (hb : b ∈ X) (hbz : b⁻¹ * (t * b * t) ∈ X ⊓ centralizer (X : Set G)) :
    ∃ p ∈ X ⊓ centralizer ({t} : Set G), ∃ w ∈ X ⊓ centralizer (X : Set G), b = p * w := by
  set z := b⁻¹ * (t * b * t) with hz
  have htb : t * b * t = b * z := by rw [hz, mul_inv_cancel_left]
  have hzt : t * z * t = z := by
    have h1 : t * z * t = (t * b * t)⁻¹ * b := by
      calc t * z * t = t * b⁻¹ * t * b * (t * t) := by rw [hz]; group
        _ = t * b⁻¹ * t * b := by rw [ht, mul_one]
        _ = (t * b * t)⁻¹ * b := by
            rw [mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right ht]
            group
    rw [h1, htb, mul_inv_rev, inv_mul_cancel_right, inv_eq_of_mul_eq_one_right (hZ z hbz)]
  have hzC : z ∈ X ⊓ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) :=
    ⟨hbz, mem_centralizer_singleton_iff.2 (by
      calc z * t = t * z * t * t := by rw [hzt]
        _ = t * z := by rw [mul_assoc, ht, mul_one])⟩
  obtain ⟨w, hw, hzw⟩ := exists_mul_conj_of_mem_center_D4 ht htX hZ hcardZ hzC
  have hwt : t * w * t ∈ X ⊓ centralizer (X : Set G) := conj_mem_center_D4 htX ht hw
  have hww : (t * w * t) * (t * w * t) = 1 := hZ _ hwt
  refine ⟨b * w, ⟨mul_mem hb hw.1, mem_centralizer_singleton_iff.2 ?_⟩, w, hw, ?_⟩
  · have e : t * (b * w) * t = b * w := by
      calc t * (b * w) * t = (t * b * t) * (t * w * t) := by
            rw [show (t * b * t) * (t * w * t) = t * b * (t * t) * w * t by group, ht, mul_one]
            group
        _ = b * z * (t * w * t) := by rw [htb]
        _ = b * w * ((t * w * t) * (t * w * t)) := by rw [hzw]; group
        _ = b * w := by rw [hww, mul_one]
    calc b * w * t = t * (b * w) * t * t := by rw [e]
      _ = t * (b * w) := by rw [mul_assoc, ht, mul_one]
  · rw [mul_assoc, hZ w hw, mul_one]

theorem mul_mul_mul_comm_D4 {M : Type*} [Group M] (hc : ∀ a b : M, a * b = b * a) (a b c d : M) :
    b * a * (c * d) = a * c * (b * d) := by
  rw [hc b a, mul_assoc, ← mul_assoc b c d, hc b c, mul_assoc c b d, ← mul_assoc a c]

theorem exists_conj_eq_of_sq_eq_one_D4 (ht : t * t = 1) (htX : t ∈ normalizer (X : Set G))
    (hZ : ∀ z ∈ X ⊓ centralizer (X : Set G), z * z = 1)
    (hX : ∀ x ∈ X, x * x ∈ X ⊓ centralizer (X : Set G))
    (hcard : Nat.card X = Nat.card (X ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2)
    (hcardZ : Nat.card (X ⊓ centralizer (X : Set G) : Subgroup G) =
      Nat.card (X ⊓ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2)
    {y : G} (hy : y ∈ X) (hty : t * y * (t * y) = 1) :
    ∃ c ∈ X, t * y = c * t * c⁻¹ := by
  classical
  set Z := X ⊓ centralizer (X : Set G) with hZdef
  set P := X ⊓ centralizer ({t} : Set G) with hPdef
  have hZX : Z ≤ X := inf_le_left
  have hPX : P ≤ X := inf_le_left
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  set Z' := Z.subgroupOf X with hZ'
  have hZ'n : Z'.Normal := ⟨fun n hn g => by
    rw [hZ', mem_subgroupOf] at hn ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← center_comm_D4 hn g.2,
      mul_inv_cancel_right]
    exact hn⟩
  have hQsq : ∀ r : X ⧸ Z', r * r = 1 := by
    intro r
    induction r using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, hZ', mem_subgroupOf,
        Subgroup.coe_mul]
      exact hX x x.2
  have hQc : ∀ r s : X ⧸ Z', r * s = s * r := by
    intro r s
    calc r * s = (r * s)⁻¹ := (inv_eq_of_mul_eq_one_right (hQsq (r * s))).symm
      _ = s⁻¹ * r⁻¹ := mul_inv_rev r s
      _ = s * r := by
          rw [inv_eq_of_mul_eq_one_right (hQsq s), inv_eq_of_mul_eq_one_right (hQsq r)]
  let σ : X →* X :=
    { toFun := fun b => ⟨t * b * t, conj_mem_D4 htX ht b.2⟩
      map_one' := Subtype.ext (by simp [ht])
      map_mul' := fun a b => Subtype.ext (by
        change t * ((a : G) * b) * t = t * a * t * (t * b * t)
        rw [show t * (a : G) * t * (t * b * t) = t * a * (t * t) * b * t by group, ht, mul_one]
        group) }
  have hσ : ∀ b : X, (σ b : G) = t * b * t := fun _ => rfl
  let ψ : X →* X ⧸ Z' :=
    { toFun := fun b => ((b⁻¹ * σ b : X) : X ⧸ Z')
      map_one' := by simp
      map_mul' := fun a b => by
        rw [show (a * b)⁻¹ * σ (a * b) = b⁻¹ * a⁻¹ * (σ a * σ b) by rw [map_mul, mul_inv_rev]]
        simp only [QuotientGroup.mk_mul]
        exact mul_mul_mul_comm_D4 hQc _ _ _ _ }
  have hψ : ∀ b : X, ψ b = ((b⁻¹ * σ b : X) : X ⧸ Z') := fun _ => rfl
  have hker : ∀ b : X, b ∈ ψ.ker ↔ (b : G)⁻¹ * (t * b * t) ∈ Z := by
    intro b
    rw [MonoidHom.mem_ker, hψ, QuotientGroup.eq_one_iff, hZ', mem_subgroupOf]
    rfl
  have hinvPZ : ∀ x ∈ X, t * x * t = x⁻¹ → x ∈ P ⊔ Z := by
    intro x hx hxt
    have hxz : x⁻¹ * (t * x * t) ∈ Z := by
      rw [hxt, ← mul_inv_rev]
      exact inv_mem (hX x hx)
    obtain ⟨p, hp, w, hw, rfl⟩ := exists_mul_of_conj_mem_center_D4 ht htX hZ hcardZ hx hxz
    exact mul_mem_sup hp hw
  have hkerG : ψ.ker.map X.subtype = P ⊔ Z := by
    apply le_antisymm
    · rintro _ ⟨b, hb, rfl⟩
      obtain ⟨p, hp, w, hw, hpw⟩ := exists_mul_of_conj_mem_center_D4 ht htX hZ hcardZ b.2
        ((hker b).1 hb)
      change (b : G) ∈ P ⊔ Z
      rw [hpw]
      exact mul_mem_sup hp hw
    · refine sup_le (fun p hp => ⟨⟨p, hPX hp⟩, (hker _).2 ?_, rfl⟩)
        (fun z hz => ⟨⟨z, hZX hz⟩, (hker _).2 ?_, rfl⟩)
      · have hpt : t * p * t = p := by
          rw [← mem_centralizer_singleton_iff.1 hp.2, mul_assoc, ht, mul_one]
        change p⁻¹ * (t * p * t) ∈ Z
        rw [hpt, inv_mul_cancel]
        exact one_mem _
      · exact mul_mem (inv_mem hz) (conj_mem_center_D4 htX ht hz)
  set K := (P ⊔ Z).subgroupOf X with hK
  set M := K.map (QuotientGroup.mk' Z') with hM
  have hrange : ψ.range ≤ M := by
    rintro _ ⟨b, rfl⟩
    have hyX : (b : G)⁻¹ * (t * b * t) ∈ X := mul_mem (inv_mem b.2) (conj_mem_D4 htX ht b.2)
    have hyt : t * ((b : G)⁻¹ * (t * b * t)) * t = ((b : G)⁻¹ * (t * b * t))⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, htinv]
      rw [show t * ((b : G)⁻¹ * (t * b * t)) * t = t * (b : G)⁻¹ * t * b * (t * t) by group, ht,
        mul_one]
      group
    exact ⟨b⁻¹ * σ b, hinvPZ _ hyX hyt, rfl⟩
  have hcardP : Nat.card ↥(P ⊔ Z) * Nat.card ↥(Z ⊓ centralizer ({t} : Set G)) =
      Nat.card P * Nat.card Z := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute P Z
      fun x hx z hz => (center_comm_D4 hz hx.1).symm).1
    have hPZ : P ⊓ Z = Z ⊓ centralizer ({t} : Set G) := by
      rw [hPdef, hZdef]
      ext x
      simp only [mem_inf]
      tauto
    rwa [hPZ] at h
  have hψcard := Subgroup.card_ker_mul_card_range ψ
  rw [← card_map_of_injective (K := ψ.ker) X.subtype_injective, hkerG] at hψcard
  have hMcard : Nat.card M * Nat.card Z = Nat.card ↥(P ⊔ Z) := by
    have h := Subgroup.card_ker_mul_card_range ((QuotientGroup.mk' Z').domRestrict K)
    rw [MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict, QuotientGroup.ker_mk'] at h
    have hZK : Z' ≤ K := fun z hz => by
      rw [hK, mem_subgroupOf]
      exact mem_sup_right hz
    have h1 : Nat.card (Z'.subgroupOf K) = Nat.card Z :=
      (Nat.card_congr (subgroupOfEquivOfLe hZK).toEquiv).trans
        (Nat.card_congr (subgroupOfEquivOfLe hZX).toEquiv)
    have h2 : Nat.card K = Nat.card ↥(P ⊔ Z) :=
      Nat.card_congr (subgroupOfEquivOfLe (sup_le hPX hZX)).toEquiv
    rw [h1, h2] at h
    rw [← hM] at h
    linarith
  have hrcard : Nat.card ψ.range = Nat.card M := by
    set z := Nat.card ↥(Z ⊓ centralizer ({t} : Set G))
    set p := Nat.card P
    have hzpos : 0 < z := Nat.card_pos
    have hppos : 0 < p := Nat.card_pos
    have hcZ : Nat.card Z = z ^ 2 := hcardZ
    rw [hcZ] at hcardP hMcard
    have hs : Nat.card ↥(P ⊔ Z) = p * z := by
      have h3 : Nat.card ↥(P ⊔ Z) * z = (p * z) * z := by rw [hcardP]; ring
      exact Nat.eq_of_mul_eq_mul_right hzpos h3
    rw [hs] at hψcard hMcard
    have hX' : Nat.card X = p ^ 2 := hcard
    rw [hX'] at hψcard
    have hm : Nat.card M * z = p := by
      have h4 : (Nat.card M * z) * z = p * z := by rw [← hMcard]; ring
      exact Nat.eq_of_mul_eq_mul_right hzpos h4
    have h5 : Nat.card ψ.range * z * p = Nat.card M * z * p := by
      calc Nat.card ψ.range * z * p = p * z * Nat.card ψ.range := by ring
        _ = p * p := by rw [hψcard, sq]
        _ = Nat.card M * z * p := by rw [hm]
    have h6 := Nat.eq_of_mul_eq_mul_right hppos h5
    exact Nat.eq_of_mul_eq_mul_right hzpos h6
  have hrM : ψ.range = M := eq_of_le_of_card_ge hrange hrcard.symm.le
  have hyt : t * y * t = y⁻¹ := by
    have h := eq_inv_of_mul_eq_one_left hty
    rw [mul_inv_rev, htinv] at h
    calc t * y * t = t * y * t * (y * y⁻¹) := by rw [mul_inv_cancel, mul_one]
      _ = (t * y * (t * y)) * y⁻¹ := by group
      _ = y⁻¹ := by rw [hty, one_mul]
  have hyM : ((⟨y, hy⟩ : X) : X ⧸ Z') ∈ M :=
    ⟨⟨y, hy⟩, hinvPZ y hy hyt, rfl⟩
  rw [← hrM] at hyM
  obtain ⟨b, hb⟩ := hyM
  rw [hψ, QuotientGroup.eq] at hb
  set z : G := (((b⁻¹ * σ b)⁻¹ * ⟨y, hy⟩ : X) : G) with hzdef
  have hzZ : z ∈ Z := by
    rw [hZ', mem_subgroupOf] at hb
    exact hb
  have hyz : y = (b : G)⁻¹ * (t * b * t) * z := by
    rw [hzdef]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hσ]
    group
  have hzt : t * z * t = z := by
    have hbX : (b : G)⁻¹ * (t * b * t) ∈ X := mul_mem (inv_mem b.2) (conj_mem_D4 htX ht b.2)
    have hc := center_comm_D4 hzZ hbX
    have hBinv : ((b : G)⁻¹ * (t * b * t))⁻¹ = t * (b : G)⁻¹ * t * b := by
      rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, htinv]
      group
    have e1 : t * y * t = ((b : G)⁻¹ * (t * b * t))⁻¹ * (t * z * t) := by
      rw [hyz, hBinv]
      group
    have e2 : y⁻¹ = ((b : G)⁻¹ * (t * b * t))⁻¹ * z⁻¹ := by
      rw [hyz, mul_inv_rev]
      calc z⁻¹ * ((b : G)⁻¹ * (t * b * t))⁻¹ =
          ((b : G)⁻¹ * (t * b * t))⁻¹ * (((b : G)⁻¹ * (t * b * t)) * z⁻¹ *
            ((b : G)⁻¹ * (t * b * t))⁻¹) := by group
        _ = ((b : G)⁻¹ * (t * b * t))⁻¹ * z⁻¹ := by
            rw [(center_comm_D4 (inv_mem hzZ) hbX).symm]
            group
    have e3 := hyt
    rw [e1, e2] at e3
    have e4 := mul_left_cancel e3
    rw [e4, inv_eq_of_mul_eq_one_right (hZ z hzZ)]
  have hzC : z ∈ X ⊓ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) :=
    ⟨hzZ, mem_centralizer_singleton_iff.2 (by
      calc z * t = t * z * t * t := by rw [hzt]
        _ = t * z := by rw [mul_assoc, ht, mul_one])⟩
  obtain ⟨w, hw, hzw⟩ := exists_mul_conj_of_mem_center_D4 ht htX hZ hcardZ hzC
  obtain ⟨x, hxdef⟩ : ∃ x : G, x = (b : G) * w := ⟨_, rfl⟩
  have hxX : x ∈ X := hxdef ▸ mul_mem b.2 hw.1
  have hyx : y = x⁻¹ * (t * x * t) := by
    rw [hyz, hzw, hxdef]
    have hwt : t * w * t ∈ Z := conj_mem_center_D4 htX ht hw
    have hbX : (b : G)⁻¹ * (t * b * t) ∈ X := mul_mem (inv_mem b.2) (conj_mem_D4 htX ht b.2)
    have hww : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hZ w hw)
    calc (b : G)⁻¹ * (t * b * t) * (w * (t * w * t)) =
        w * ((b : G)⁻¹ * (t * b * t)) * (t * w * t) := by
          rw [← mul_assoc, center_comm_D4 hw hbX]
      _ = w⁻¹ * (b : G)⁻¹ * (t * b * t) * (t * w * t) := by rw [hww]; group
      _ = ((b : G) * w)⁻¹ * (t * ((b : G) * w) * t) := by
          rw [show w⁻¹ * (b : G)⁻¹ * (t * b * t) * (t * w * t) =
            w⁻¹ * (b : G)⁻¹ * t * b * (t * t) * w * t by group, ht, mul_one]
          group
  refine ⟨t * x⁻¹ * t, conj_mem_D4 htX ht (inv_mem hxX), ?_⟩
  have hinv' : (t * x⁻¹ * t)⁻¹ = t * x * t := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, htinv]
    group
  rw [hyx, hinv', show t * x⁻¹ * t * t * (t * x * t) = t * x⁻¹ * (t * t) * t * x * t by group, ht,
    mul_one]
  group

omit [Finite G] in
theorem commutator_mem_center_D4 (hX : ∀ x ∈ X, x * x ∈ X ⊓ centralizer (X : Set G)) {a b : G}
    (ha : a ∈ X) (hb : b ∈ X) : a * b * a⁻¹ * b⁻¹ ∈ X ⊓ centralizer (X : Set G) := by
  have hza := hX a ha
  have hzb := hX b hb
  have hzab := hX _ (mul_mem ha hb)
  have h1 : a⁻¹ = (a * a)⁻¹ * a := by group
  have h2 : b⁻¹ = (b * b)⁻¹ * b := by group
  have hc1 := center_comm_D4 (inv_mem hza) (mul_mem ha hb)
  have hc2 := center_comm_D4 (inv_mem hzb) (mul_mem (mul_mem ha hb) ha)
  have e : a * b * a⁻¹ * b⁻¹ = (a * a)⁻¹ * (b * b)⁻¹ * (a * b * (a * b)) := by
    calc a * b * a⁻¹ * b⁻¹ = a * b * ((a * a)⁻¹ * a) * ((b * b)⁻¹ * b) := by rw [← h1, ← h2]
      _ = (a * b * (a * a)⁻¹) * a * (b * b)⁻¹ * b := by group
      _ = ((a * a)⁻¹ * (a * b)) * a * (b * b)⁻¹ * b := by rw [hc1]
      _ = (a * a)⁻¹ * ((a * b * a) * (b * b)⁻¹) * b := by group
      _ = (a * a)⁻¹ * ((b * b)⁻¹ * (a * b * a)) * b := by rw [hc2]
      _ = (a * a)⁻¹ * (b * b)⁻¹ * (a * b * (a * b)) := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem hza) (inv_mem hzb)) hzab

theorem inf_normalizer_le_sup_center_D4 (ht : t * t = 1) (htX : t ∈ normalizer (X : Set G))
    (hZ : ∀ z ∈ X ⊓ centralizer (X : Set G), z * z = 1)
    (hcardZ : Nat.card (X ⊓ centralizer (X : Set G) : Subgroup G) =
      Nat.card (X ⊓ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2)
    (hCP : X ⊓ centralizer ((X ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) ≤
      X ⊓ centralizer (X : Set G)) :
    X ⊓ normalizer ((X ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) ≤
      (X ⊓ centralizer ({t} : Set G)) ⊔ (X ⊓ centralizer (X : Set G)) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rintro x ⟨hxX, hxN⟩
  have hy : t * x * t ∈ X := conj_mem_D4 htX ht hxX
  have hxy : x⁻¹ * (t * x * t) ∈ X ⊓ centralizer (X : Set G) := by
    refine hCP (Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hxX) hy,
      mem_centralizer_iff.2 fun p hp => ?_⟩)
    have hpt : t * p * t = p := by
      rw [← mem_centralizer_singleton_iff.1 hp.2, mul_assoc, ht, mul_one]
    have hcP : x * p * x⁻¹ * p⁻¹ ∈ X ⊓ centralizer ({t} : Set G) :=
      mul_mem ((mem_normalizer_iff.1 hxN p).1 hp) (inv_mem hp)
    have hct : t * (x * p * x⁻¹ * p⁻¹) * t = x * p * x⁻¹ * p⁻¹ := by
      rw [← mem_centralizer_singleton_iff.1 hcP.2, mul_assoc, ht, mul_one]
    have e1 : (t * x * t) * p * (t * x * t)⁻¹ = x * p * x⁻¹ := by
      calc (t * x * t) * p * (t * x * t)⁻¹ = t * (x * (t * p * t) * x⁻¹) * t := by
            rw [mul_inv_rev, mul_inv_rev, htinv]
            group
        _ = t * ((x * p * x⁻¹ * p⁻¹) * p) * t := by rw [hpt]; group
        _ = (t * (x * p * x⁻¹ * p⁻¹) * t) * (t * p * t) := by
            rw [show (t * (x * p * x⁻¹ * p⁻¹) * t) * (t * p * t) =
              t * (x * p * x⁻¹ * p⁻¹) * (t * t) * p * t by group, ht, mul_one]
            group
        _ = x * p * x⁻¹ := by rw [hct, hpt]; group
    calc p * (x⁻¹ * (t * x * t)) = x⁻¹ * (x * p * x⁻¹) * (t * x * t) := by group
      _ = x⁻¹ * ((t * x * t) * p * (t * x * t)⁻¹) * (t * x * t) := by rw [e1]
      _ = x⁻¹ * (t * x * t) * p := by group
  obtain ⟨p, hp, w, hw, rfl⟩ := exists_mul_of_conj_mem_center_D4 ht htX hZ hcardZ hxX hxy
  exact mul_mem_sup hp hw

end Norm

section Heis

structure HeisLike (X : Subgroup G) (k : ℕ) : Prop where
  card_eq : Nat.card X = k ^ 3
  card_center : Nat.card (X ⊓ centralizer (X : Set G) : Subgroup G) = k
  center_mul_self : ∀ z ∈ X ⊓ centralizer (X : Set G), z * z = 1
  mul_self_mem : ∀ x ∈ X, x * x ∈ X ⊓ centralizer (X : Set G)
  mem_center : ∀ a ∈ X, ∀ b ∈ X, a * b ≠ b * a → ∀ c ∈ X, c * a = a * c → c * b = b * c →
    c ∈ X ⊓ centralizer (X : Set G)

section Roots

variable {K : Type*} [Field K] (hK2 : ∀ a : K, a + a = 0) {x y w : K → G}
  (hx : ∀ a b, x (a + b) = x a * x b) (hy : ∀ a b, y (a + b) = y a * y b)
  (hw : ∀ a b, w (a + b) = w a * w b) (hwx : ∀ c a, w c * x a = x a * w c)
  (hwy : ∀ c b, w c * y b = y b * w c) (hxy : ∀ a b, x a * y b = w (a * b) * y b * x a)
include hK2 hx hy hw hwx hwy hxy

theorem heis_mul_D4 (a b c a' b' c' : K) :
    w c * x a * y b * (w c' * x a' * y b') = w (c + c' + a' * b) * x (a + a') * y (b + b') := by
  have hw0 : ∀ e : K, w e * w e = 1 := fun e => by
    rw [← hw, hK2]
    have h := hw 0 0
    rw [add_zero] at h
    exact (left_eq_mul.1 h)
  have hyx : y b * x a' = w (a' * b) * x a' * y b := by
    have h := hxy a' b
    calc y b * x a' = w (a' * b) * (w (a' * b) * y b * x a') := by
          rw [← mul_assoc, ← mul_assoc, hw0, one_mul]
      _ = w (a' * b) * x a' * y b := by rw [← h, mul_assoc]
  calc w c * x a * y b * (w c' * x a' * y b') =
      w c * x a * (y b * w c') * x a' * y b' := by group
    _ = w c * (x a * w c') * (y b * x a') * y b' := by rw [← hwy]; group
    _ = w c * w c' * x a * (w (a' * b) * x a' * y b) * y b' := by rw [hyx, ← hwx]; group
    _ = w c * w c' * (x a * w (a' * b)) * x a' * (y b * y b') := by group
    _ = w (c + c' + a' * b) * x (a + a') * y (b + b') := by
        rw [← hwx, hw, hw, hx, hy]
        group

theorem heis_commute_iff_D4 (hwinj : Function.Injective w) (a b c a' b' c' : K) :
    w c * x a * y b * (w c' * x a' * y b') = w c' * x a' * y b' * (w c * x a * y b) ↔
      a' * b = a * b' := by
  rw [heis_mul_D4 hK2 hx hy hw hwx hwy hxy, heis_mul_D4 hK2 hx hy hw hwx hwy hxy, add_comm a,
    add_comm b, mul_left_inj, mul_left_inj]
  constructor
  · intro h
    have h1 := hwinj h
    linear_combination h1
  · intro h
    congr 1
    rw [h]
    ring

theorem heisLike_of_roots [Finite K] (hwinj : Function.Injective w) {X : Subgroup G}
    (hxX : ∀ a, x a ∈ X) (hyX : ∀ b, y b ∈ X) (hwX : ∀ c, w c ∈ X)
    (hmem : ∀ s ∈ X, ∃ a b c, s = w c * x a * y b) (hcard : Nat.card X = Nat.card K ^ 3) :
    HeisLike X (Nat.card K) := by
  classical
  have hcomm := heis_commute_iff_D4 hK2 hx hy hw hwx hwy hxy hwinj
  have hx0 : x 0 = 1 := by
    have h := hx 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hy0 : y 0 = 1 := by
    have h := hy 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hw0 : w 0 = 1 := by
    have h := hw 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hwc : ∀ c, w c = w c * x 0 * y 0 := fun c => by rw [hx0, hy0, mul_one, mul_one]
  have hxc : ∀ a, x a = w 0 * x a * y 0 := fun a => by rw [hw0, hy0, one_mul, mul_one]
  have hyc : ∀ b, y b = w 0 * x 0 * y b := fun b => by rw [hw0, hx0, one_mul, one_mul]
  have hcenter : ∀ s, s ∈ X ⊓ centralizer (X : Set G) ↔ ∃ c, w c = s := by
    intro s
    constructor
    · rintro ⟨hs, hsc⟩
      obtain ⟨a, b, c, rfl⟩ := hmem _ hs
      have h1 := mem_centralizer_iff.1 hsc _ (hxX 1)
      have h2 := mem_centralizer_iff.1 hsc _ (hyX 1)
      rw [hxc 1] at h1
      rw [hyc 1] at h2
      have e1 : b = 0 := by
        have h3 := (hcomm 1 0 0 a b c).1 h1
        rw [mul_zero, one_mul] at h3
        exact h3.symm
      have e2 : a = 0 := by
        have h3 := (hcomm 0 1 0 a b c).1 h2
        rw [mul_one, zero_mul] at h3
        exact h3
      subst e1
      subst e2
      exact ⟨c, by rw [hx0, hy0, mul_one, mul_one]⟩
    · rintro ⟨c, rfl⟩
      refine ⟨hwX c, mem_centralizer_iff.2 fun s hs => ?_⟩
      obtain ⟨a, b, c', rfl⟩ := hmem s hs
      rw [hwc c]
      exact (hcomm a b c' 0 0 c).2 (by ring)
  refine ⟨hcard, ?_, ?_, ?_, ?_⟩
  ·
    exact (Nat.card_congr (Equiv.subtypeEquivRight hcenter)).trans
      (Nat.card_range_of_injective hwinj)
  · intro z hz
    obtain ⟨c, rfl⟩ := (hcenter z).1 hz
    rw [← hw, hK2, hw0]
  · intro s hs
    obtain ⟨a, b, c, rfl⟩ := hmem s hs
    rw [hcenter, heis_mul_D4 hK2 hx hy hw hwx hwy hxy]
    simp only [hK2, zero_add, hx0, hy0, mul_one]
    exact ⟨_, rfl⟩
  · intro s₁ hs₁ s₂ hs₂ hne s₃ hs₃ h1 h2
    obtain ⟨a₁, b₁, c₁, rfl⟩ := hmem _ hs₁
    obtain ⟨a₂, b₂, c₂, rfl⟩ := hmem _ hs₂
    obtain ⟨a₃, b₃, c₃, rfl⟩ := hmem _ hs₃
    have hne' : a₂ * b₁ ≠ a₁ * b₂ := fun h => hne ((hcomm a₁ b₁ c₁ a₂ b₂ c₂).2 h)
    have e1 := (hcomm a₃ b₃ c₃ a₁ b₁ c₁).1 h1
    have e2 := (hcomm a₃ b₃ c₃ a₂ b₂ c₂).1 h2
    have hd : a₂ * b₁ - a₁ * b₂ ≠ 0 := sub_ne_zero.2 hne'
    have ha : a₃ = 0 := by
      have h3 : a₃ * (a₂ * b₁ - a₁ * b₂) = 0 := by linear_combination a₁ * e2 - a₂ * e1
      exact (mul_eq_zero.1 h3).resolve_right hd
    have hb : b₃ = 0 := by
      have h3 : b₃ * (a₂ * b₁ - a₁ * b₂) = 0 := by linear_combination b₁ * e2 - b₂ * e1
      exact (mul_eq_zero.1 h3).resolve_right hd
    rw [ha, hb, hx0, hy0, mul_one, mul_one]
    exact (hcenter _).2 ⟨c₃, rfl⟩

end Roots

section Transport

variable {G' : Type*} [Group G'] (φ : G →* G') {X : Subgroup G}

theorem eq_of_map_eq_D4 (hφ : ∀ x ∈ X, φ x = 1 → x = 1) {a b : G} (ha : a ∈ X) (hb : b ∈ X)
    (h : φ a = φ b) : a = b :=
  mul_inv_eq_one.1 (hφ _ (mul_mem ha (inv_mem hb)) (by rw [map_mul, map_inv, h, mul_inv_cancel]))

theorem card_map_of_injOn_D4 (hφ : ∀ x ∈ X, φ x = 1 → x = 1) {Y : Subgroup G} (hYX : Y ≤ X) :
    Nat.card (Y.map φ) = Nat.card Y := by
  refine (Nat.card_congr (Equiv.ofBijective (φ.subgroupMap Y)
    ⟨fun a b hab => Subtype.ext ?_, φ.subgroupMap_surjective Y⟩)).symm
  exact eq_of_map_eq_D4 φ hφ (hYX a.2) (hYX b.2) (congrArg Subtype.val hab)

theorem map_mem_center_iff_D4 (hφ : ∀ x ∈ X, φ x = 1 → x = 1) {x : G} (hx : x ∈ X) :
    φ x ∈ X.map φ ⊓ centralizer (X.map φ : Set G') ↔ x ∈ X ⊓ centralizer (X : Set G) := by
  constructor
  · rintro ⟨-, hc⟩
    refine ⟨hx, mem_centralizer_iff.2 fun y hy => eq_of_map_eq_D4 φ hφ (mul_mem hy hx)
      (mul_mem hx hy) ?_⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.1 hc _ ⟨y, hy, rfl⟩
  · rintro ⟨-, hc⟩
    refine ⟨⟨x, hx, rfl⟩, mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hc y hy]

theorem map_center_eq_D4 (hφ : ∀ x ∈ X, φ x = 1 → x = 1) :
    (X ⊓ centralizer (X : Set G)).map φ = X.map φ ⊓ centralizer (X.map φ : Set G') := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (map_mem_center_iff_D4 φ hφ hx.1).2 hx
  · intro hy
    obtain ⟨x, hx, rfl⟩ := hy.1
    exact ⟨x, (map_mem_center_iff_D4 φ hφ hx).1 hy, rfl⟩

theorem HeisLike.map_iff (hφ : ∀ x ∈ X, φ x = 1 → x = 1) {k : ℕ} :
    HeisLike (X.map φ) k ↔ HeisLike X k := by
  have hcard := card_map_of_injOn_D4 φ hφ le_rfl
  have hZcard := card_map_of_injOn_D4 φ hφ (Y := X ⊓ centralizer (X : Set G)) inf_le_left
  rw [map_center_eq_D4 φ hφ] at hZcard
  have hcomm : ∀ {a b : G}, a ∈ X → b ∈ X → (φ a * φ b = φ b * φ a ↔ a * b = b * a) :=
    fun ha hb => by
      rw [← map_mul, ← map_mul]
      exact ⟨eq_of_map_eq_D4 φ hφ (mul_mem ha hb) (mul_mem hb ha), fun h => by rw [h]⟩
  constructor
  · intro h
    refine ⟨hcard ▸ h.card_eq, hZcard ▸ h.card_center, fun z hz => ?_, fun x hx => ?_,
      fun a ha b hb hab c hc hca hcb => ?_⟩
    · have h1 := h.center_mul_self _ ((map_mem_center_iff_D4 φ hφ hz.1).2 hz)
      rw [← map_mul] at h1
      exact hφ _ (mul_mem hz.1 hz.1) h1
    · have h1 := h.mul_self_mem _ ⟨x, hx, rfl⟩
      rw [← map_mul] at h1
      exact (map_mem_center_iff_D4 φ hφ (mul_mem hx hx)).1 h1
    · have h1 := h.mem_center _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ (fun e => hab ((hcomm ha hb).1 e))
        _ ⟨c, hc, rfl⟩ ((hcomm hc ha).2 hca) ((hcomm hc hb).2 hcb)
      exact (map_mem_center_iff_D4 φ hφ hc).1 h1
  · intro h
    refine ⟨hcard ▸ h.card_eq, hZcard ▸ h.card_center, fun z hz => ?_, fun x hx => ?_,
      fun a ha b hb hab c hc hca hcb => ?_⟩
    · obtain ⟨z₀, hz₀, rfl⟩ := hz.1
      rw [← map_mul, h.center_mul_self _ ((map_mem_center_iff_D4 φ hφ hz₀).1 hz), map_one]
    · obtain ⟨x₀, hx₀, rfl⟩ := hx
      rw [← map_mul]
      exact (map_mem_center_iff_D4 φ hφ (mul_mem hx₀ hx₀)).2 (h.mul_self_mem _ hx₀)
    · obtain ⟨a₀, ha₀, rfl⟩ := ha
      obtain ⟨b₀, hb₀, rfl⟩ := hb
      obtain ⟨c₀, hc₀, rfl⟩ := hc
      exact (map_mem_center_iff_D4 φ hφ hc₀).2 (h.mem_center _ ha₀ _ hb₀
        (fun e => hab ((hcomm ha₀ hb₀).2 e)) _ hc₀ ((hcomm hc₀ ha₀).1 hca)
        ((hcomm hc₀ hb₀).1 hcb))

omit [Group G'] in
theorem HeisLike.congr {G' : Type*} [Group G'] {Y : Subgroup G'} (e : X ≃* Y) {k : ℕ} :
    HeisLike X k ↔ HeisLike Y k := by
  have hX : (⊤ : Subgroup X).map X.subtype = X := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  have hY : (⊤ : Subgroup Y).map Y.subtype = Y := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  have he : (⊤ : Subgroup X).map e.toMonoidHom = ⊤ := map_top_of_surjective _ e.surjective
  have h1 := HeisLike.map_iff X.subtype (X := ⊤) (fun x _ hx => Subtype.ext hx) (k := k)
  have h2 := HeisLike.map_iff e.toMonoidHom (X := ⊤) (fun x _ hx => e.injective
    (hx.trans (map_one e).symm)) (k := k)
  have h3 := HeisLike.map_iff Y.subtype (X := ⊤) (fun x _ hx => Subtype.ext hx) (k := k)
  rw [hX] at h1
  rw [he] at h2
  rw [hY] at h3
  rw [h1, ← h2, h3]

end Transport

theorem injective_of_card_roots_D4 {K : Type*} [Field K] [Finite K] {x y w : K → G}
    {X : Subgroup G} (hxX : ∀ a, x a ∈ X) (hyX : ∀ b, y b ∈ X)
    (hwX : ∀ c, w c ∈ X) (hmem : ∀ s ∈ X, ∃ a b c, s = w c * x a * y b)
    (hcard : Nat.card X = Nat.card K ^ 3) : Function.Injective w := by
  classical
  let μ : K × K × K → X := fun p => ⟨w p.2.2 * x p.1 * y p.2.1,
    mul_mem (mul_mem (hwX _) (hxX _)) (hyX _)⟩
  have hμ : Function.Surjective μ := by
    intro s
    obtain ⟨a, b, c, hs⟩ := hmem s s.2
    exact ⟨(a, b, c), Subtype.ext hs.symm⟩
  have hbij := hμ.bijective_of_nat_card_le (by
    rw [hcard, Nat.card_prod, Nat.card_prod]
    ring_nf
    exact le_rfl)
  intro c c' hcc
  have h1 : μ (0, 0, c) = μ (0, 0, c') := Subtype.ext (by
    change w c * x 0 * y 0 = w c' * x 0 * y 0
    rw [hcc])
  have h2 := hbij.1 h1
  simp only [Prod.mk.injEq, true_and] at h2
  exact h2

structure SylowShape (X P : Subgroup G) (k : ℕ) : Prop where
  card_eq : Nat.card X = k ^ 6
  card_center : Nat.card (X ⊓ centralizer (X : Set G) : Subgroup G) = k ^ 2
  center_mul_self : ∀ z ∈ X ⊓ centralizer (X : Set G), z * z = 1
  mul_self_mem : ∀ x ∈ X, x * x ∈ X ⊓ centralizer (X : Set G)
  inf_centralizer_le : X ⊓ centralizer (P : Set G) ≤ X ⊓ centralizer (X : Set G)

theorem HeisLike.sylowShape {X P : Subgroup G} {k : ℕ} (hX : HeisLike X (k ^ 2)) (hPX : P ≤ X)
    {a b : G} (ha : a ∈ P) (hb : b ∈ P) (hab : a * b ≠ b * a) : SylowShape X P k := by
  refine ⟨by rw [hX.card_eq, ← pow_mul], by rw [hX.card_center], hX.center_mul_self,
    hX.mul_self_mem, fun y hy => ?_⟩
  exact hX.mem_center a (hPX ha) b (hPX hb) hab y hy.1 (mem_centralizer_iff.1 hy.2 a ha).symm
    (mem_centralizer_iff.1 hy.2 b hb).symm

section ShapeTransport

variable {G' : Type*} [Group G'] (φ : G →* G') {X P : Subgroup G}

theorem SylowShape.map_iff (hφ : ∀ x ∈ X, φ x = 1 → x = 1) (hPX : P ≤ X) {k : ℕ} :
    SylowShape (X.map φ) (P.map φ) k ↔ SylowShape X P k := by
  have hcard := card_map_of_injOn_D4 φ hφ le_rfl
  have hZcard := card_map_of_injOn_D4 φ hφ (Y := X ⊓ centralizer (X : Set G)) inf_le_left
  rw [map_center_eq_D4 φ hφ] at hZcard
  have hC : ∀ y ∈ X, φ y ∈ centralizer (P.map φ : Set G') ↔ y ∈ centralizer (P : Set G) := by
    intro y hy
    constructor
    · intro h
      rw [mem_centralizer_iff]
      intro p hp
      refine eq_of_map_eq_D4 φ hφ (mul_mem (hPX hp) hy) (mul_mem hy (hPX hp)) ?_
      rw [map_mul, map_mul]
      exact mem_centralizer_iff.1 h _ ⟨p, hp, rfl⟩
    · intro h
      rw [mem_centralizer_iff]
      rintro _ ⟨p, hp, rfl⟩
      rw [← map_mul, ← map_mul, mem_centralizer_iff.1 h p hp]
  constructor
  · intro h
    refine ⟨hcard ▸ h.card_eq, hZcard ▸ h.card_center, fun z hz => ?_, fun x hx => ?_,
      fun y hy => ?_⟩
    · have h1 := h.center_mul_self _ ((map_mem_center_iff_D4 φ hφ hz.1).2 hz)
      rw [← map_mul] at h1
      exact hφ _ (mul_mem hz.1 hz.1) h1
    · have h1 := h.mul_self_mem _ ⟨x, hx, rfl⟩
      rw [← map_mul] at h1
      exact (map_mem_center_iff_D4 φ hφ (mul_mem hx hx)).1 h1
    · exact (map_mem_center_iff_D4 φ hφ hy.1).1
        (h.inf_centralizer_le ⟨⟨y, hy.1, rfl⟩, (hC y hy.1).2 hy.2⟩)
  · intro h
    refine ⟨hcard ▸ h.card_eq, hZcard ▸ h.card_center, fun z hz => ?_, fun x hx => ?_,
      fun y hy => ?_⟩
    · obtain ⟨z₀, hz₀, rfl⟩ := hz.1
      rw [← map_mul, h.center_mul_self _ ((map_mem_center_iff_D4 φ hφ hz₀).1 hz), map_one]
    · obtain ⟨x₀, hx₀, rfl⟩ := hx
      rw [← map_mul]
      exact (map_mem_center_iff_D4 φ hφ (mul_mem hx₀ hx₀)).2 (h.mul_self_mem _ hx₀)
    · obtain ⟨y₀, hy₀, rfl⟩ := hy.1
      exact (map_mem_center_iff_D4 φ hφ hy₀).2
        (h.inf_centralizer_le ⟨hy₀, (hC y₀ hy₀).1 hy.2⟩)

end ShapeTransport

theorem sylowShape_of_swap [Finite G] {A B : Subgroup G} {s : G} (hs : s * s = 1) {k : ℕ}
    (hA : HeisLike A k) (hB : B = A.map (MulAut.conj s).toMonoidHom)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥) :
    SylowShape (A ⊔ B) ((A ⊔ B) ⊓ centralizer ({s} : Set G)) k := by
  classical
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hBh : HeisLike B k := by
    rw [hB]
    exact (HeisLike.map_iff (MulAut.conj s).toMonoidHom fun x _ hx =>
      (MulAut.conj s).injective (hx.trans (map_one _).symm)).2 hA
  obtain ⟨hcardAB, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hAB
  rw [hinf, card_bot, mul_one] at hcardAB
  have hdec : ∀ x ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
    intro x hx
    have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
    rw [hset] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    exact ⟨a, ha, b, hb, rfl⟩
  have huniq : ∀ {a a' b b' : G}, a ∈ A → a' ∈ A → b ∈ B → b' ∈ B → a * b = a' * b' →
      a = a' ∧ b = b' := by
    intro a a' b b' ha ha' hb hb' h
    have h1 : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
        _ = b' * b⁻¹ := by group
    have h2 : a'⁻¹ * a ∈ A ⊓ B :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha') ha, h1 ▸ mul_mem hb' (inv_mem hb)⟩
    rw [hinf, mem_bot] at h2
    have e1 : a = a' := by
      calc a = a' * (a'⁻¹ * a) := by group
        _ = a' := by rw [h2, mul_one]
    refine ⟨e1, ?_⟩
    subst e1
    exact (mul_left_cancel h).symm ▸ rfl
  have hZ : ∀ x, x ∈ (A ⊔ B) ⊓ centralizer ((A ⊔ B : Subgroup G) : Set G) ↔
      x ∈ (A ⊓ centralizer (A : Set G)) ⊔ (B ⊓ centralizer (B : Set G)) := by
    intro x
    constructor
    · rintro ⟨hx, hxc⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := hdec x hx
      have haZ : a ∈ A ⊓ centralizer (A : Set G) := by
        refine ⟨ha, mem_centralizer_iff.2 fun a' ha' => ?_⟩
        have h1 := mem_centralizer_iff.1 hxc a' (mem_sup_left ha')
        have h2 : (a' * a) * b = (a * a') * b := by
          calc (a' * a) * b = a' * (a * b) := by group
            _ = a * b * a' := h1
            _ = a * (b * a') := by group
            _ = a * (a' * b) := by rw [(hAB a' ha' b hb).symm]
            _ = (a * a') * b := by group
        exact mul_right_cancel h2
      have hbZ : b ∈ B ⊓ centralizer (B : Set G) := by
        refine ⟨hb, mem_centralizer_iff.2 fun b' hb' => ?_⟩
        have h1 := mem_centralizer_iff.1 hxc b' (mem_sup_right hb')
        have h2 : a * (b' * b) = a * (b * b') := by
          calc a * (b' * b) = (a * b') * b := by group
            _ = (b' * a) * b := by rw [hAB a ha b' hb']
            _ = b' * (a * b) := by group
            _ = a * b * b' := h1
            _ = a * (b * b') := by group
        exact mul_left_cancel h2
      exact mul_mem_sup haZ hbZ
    · intro hx
      have hle : (A ⊓ centralizer (A : Set G)) ⊔ (B ⊓ centralizer (B : Set G)) ≤
          (A ⊔ B) ⊓ centralizer ((A ⊔ B : Subgroup G) : Set G) := by
        refine sup_le (le_inf (inf_le_left.trans le_sup_left) ?_)
          (le_inf (inf_le_left.trans le_sup_right) ?_)
        · rw [← le_centralizer_iff]
          refine sup_le (le_centralizer_iff.1 inf_le_right) ?_
          rw [le_centralizer_iff]
          intro z hz
          rw [mem_centralizer_iff]
          intro b hb
          exact (hAB z hz.1 b hb).symm
        · rw [← le_centralizer_iff]
          refine sup_le ?_ (le_centralizer_iff.1 inf_le_right)
          rw [le_centralizer_iff]
          intro z hz
          rw [mem_centralizer_iff]
          intro a ha
          exact hAB a ha z hz.1
      exact hle hx
  have hZeq : (A ⊔ B) ⊓ centralizer ((A ⊔ B : Subgroup G) : Set G) =
      (A ⊓ centralizer (A : Set G)) ⊔ (B ⊓ centralizer (B : Set G)) := by
    ext x
    exact hZ x
  have hZc : ∀ z ∈ A ⊓ centralizer (A : Set G), ∀ z' ∈ B ⊓ centralizer (B : Set G),
      z * z' = z' * z := fun z hz z' hz' => hAB z hz.1 z' hz'.1
  obtain ⟨hcardZ, hsetZ⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hZc
  have hinfZ : (A ⊓ centralizer (A : Set G)) ⊓ (B ⊓ centralizer (B : Set G)) = ⊥ :=
    le_bot_iff.1 (hinf ▸ inf_le_inf inf_le_left inf_le_left)
  rw [hinfZ, card_bot, mul_one, hA.card_center, hBh.card_center] at hcardZ
  have hZmem : ∀ z ∈ (A ⊓ centralizer (A : Set G)) ⊔ (B ⊓ centralizer (B : Set G)),
      ∃ za ∈ A ⊓ centralizer (A : Set G), ∃ zb ∈ B ⊓ centralizer (B : Set G), z = za * zb := by
    intro z hz
    have hz' : z ∈ (((A ⊓ centralizer (A : Set G)) ⊔ (B ⊓ centralizer (B : Set G)) :
        Subgroup G) : Set G) := hz
    rw [hsetZ] at hz'
    obtain ⟨za, hza, zb, hzb, rfl⟩ := hz'
    exact ⟨za, hza, zb, hzb, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hcardAB, hA.card_eq, hBh.card_eq]
    ring
  · rw [hZeq, hcardZ]
    ring
  · intro z hz
    rw [hZeq] at hz
    obtain ⟨za, hza, zb, hzb, rfl⟩ := hZmem z hz
    calc za * zb * (za * zb) = (za * za) * (zb * zb) := by
          rw [show za * zb * (za * zb) = za * (zb * za) * zb by group, ← hZc za hza zb hzb]
          group
      _ = 1 := by rw [hA.center_mul_self za hza, hBh.center_mul_self zb hzb, one_mul]
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec x hx
    rw [hZeq]
    have e : a * b * (a * b) = (a * a) * (b * b) := by
      rw [show a * b * (a * b) = a * (b * a) * b by group, ← hAB a ha b hb]
      group
    rw [e]
    exact mul_mem_sup (hA.mul_self_mem a ha) (hBh.mul_self_mem b hb)
  · rintro y ⟨hy, hyc⟩
    rw [hZeq]
    obtain ⟨a', ha', b', hb', rfl⟩ := hdec y hy
    have hdiag : ∀ a ∈ A, a * (s * a * s) ∈ (A ⊔ B) ⊓ centralizer ({s} : Set G) := by
      intro a ha
      have hsa : s * a * s ∈ B := by
        rw [hB]
        refine ⟨a, ha, ?_⟩
        simp [hsinv]
      refine ⟨mul_mem_sup ha hsa, mem_centralizer_singleton_iff.2 ?_⟩
      have h := hAB a ha _ hsa
      have e : s * (a * (s * a * s)) * s = a * (s * a * s) := by
        calc s * (a * (s * a * s)) * s = (s * a * s) * a * (s * s) := by group
          _ = (s * a * s) * a := by rw [hs, mul_one]
          _ = a * (s * a * s) := h.symm
      calc a * (s * a * s) * s = (s * (a * (s * a * s)) * s) * s := by rw [e]
        _ = s * (a * (s * a * s)) * (s * s) := by group
        _ = s * (a * (s * a * s)) := by rw [hs, mul_one]
    have hdec2 : ∀ a ∈ A, a' * a = a * a' ∧ b' * (s * a * s) = (s * a * s) * b' := by
      intro a ha
      have hsa : s * a * s ∈ B := by
        rw [hB]
        refine ⟨a, ha, ?_⟩
        simp [hsinv]
      have h1 := mem_centralizer_iff.1 hyc _ (hdiag a ha)
      have h2 : (a * a') * ((s * a * s) * b') = (a' * a) * (b' * (s * a * s)) := by
        calc (a * a') * ((s * a * s) * b') = a * (a' * (s * a * s)) * b' := by group
          _ = a * ((s * a * s) * a') * b' := by rw [hAB a' ha' _ hsa]
          _ = a * (s * a * s) * (a' * b') := by group
          _ = a' * b' * (a * (s * a * s)) := h1
          _ = a' * (b' * a) * (s * a * s) := by group
          _ = a' * (a * b') * (s * a * s) := by rw [hAB a ha b' hb']
          _ = (a' * a) * (b' * (s * a * s)) := by group
      have h3 := huniq (mul_mem ha ha') (mul_mem ha' ha) (mul_mem hsa hb') (mul_mem hb' hsa) h2
      exact ⟨h3.1.symm, h3.2.symm⟩
    have haZ : a' ∈ A ⊓ centralizer (A : Set G) :=
      ⟨ha', mem_centralizer_iff.2 fun a ha => (hdec2 a ha).1.symm⟩
    have hbZ : b' ∈ B ⊓ centralizer (B : Set G) := by
      refine ⟨hb', mem_centralizer_iff.2 fun b hb => ?_⟩
      have hb'' : b ∈ A.map (MulAut.conj s).toMonoidHom := hB ▸ hb
      obtain ⟨a, ha, rfl⟩ := hb''
      have e : (MulAut.conj s).toMonoidHom a = s * a * s := by simp [hsinv]
      rw [e]
      exact (hdec2 a ha).2.symm
    exact mul_mem_sup haZ hbZ

theorem heisLike_of_swap_diag [Finite G] {A B : Subgroup G} {s : G} (hs : s * s = 1) {k : ℕ}
    (hB : B = A.map (MulAut.conj s).toMonoidHom)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥)
    (hP : HeisLike ((A ⊔ B) ⊓ centralizer ({s} : Set G)) k) : HeisLike A k := by
  classical
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hsa : ∀ a ∈ A, s * a * s ∈ B := fun a ha => by
    rw [hB]
    exact ⟨a, ha, by simp [hsinv]⟩
  have hsb : ∀ b ∈ B, s * b * s ∈ A := fun b hb => by
    have hb' : b ∈ A.map (MulAut.conj s).toMonoidHom := hB ▸ hb
    obtain ⟨a, ha, rfl⟩ := hb'
    have e : s * (MulAut.conj s).toMonoidHom a * s = a := by
      change s * (s * a * s⁻¹) * s = a
      rw [hsinv, show s * (s * a * s) * s = (s * s) * a * (s * s) by group, hs, one_mul,
        mul_one]
    rw [e]
    exact ha
  have hdiag : ∀ a ∈ A, a * (s * a * s) ∈ (A ⊔ B) ⊓ centralizer ({s} : Set G) := by
    intro a ha
    refine ⟨mul_mem_sup ha (hsa a ha), mem_centralizer_singleton_iff.2 ?_⟩
    have h := hAB a ha _ (hsa a ha)
    have e : s * (a * (s * a * s)) * s = a * (s * a * s) := by
      calc s * (a * (s * a * s)) * s = (s * a * s) * a * (s * s) := by group
        _ = (s * a * s) * a := by rw [hs, mul_one]
        _ = a * (s * a * s) := h.symm
    calc a * (s * a * s) * s = (s * (a * (s * a * s)) * s) * s := by rw [e]
      _ = s * (a * (s * a * s)) * (s * s) := by group
      _ = s * (a * (s * a * s)) := by rw [hs, mul_one]
  let μ : A →* ((A ⊔ B) ⊓ centralizer ({s} : Set G) : Subgroup G) :=
    { toFun := fun a => ⟨a * (s * a * s), hdiag a a.2⟩
      map_one' := Subtype.ext (by simp [hs])
      map_mul' := fun a a' => Subtype.ext (by
        change (a : G) * a' * (s * (a * a') * s) = a * (s * a * s) * (a' * (s * a' * s))
        have h := hAB a' a'.2 _ (hsa a a.2)
        calc (a : G) * a' * (s * (a * a') * s) = a * (a' * (s * a * s)) * (s * a' * s) := by
              rw [show s * ((a : G) * a') * s = (s * a * s) * (s * a' * s) by
                rw [show (s * (a : G) * s) * (s * a' * s) = s * a * (s * s) * a' * s by group, hs,
                  mul_one]
                group]
              group
          _ = a * ((s * a * s) * a') * (s * a' * s) := by rw [h]
          _ = a * (s * a * s) * (a' * (s * a' * s)) := by group) }
  have hμinj : Function.Injective μ := by
    intro a a' haa
    have h1 : (a : G) * (s * a * s) = a' * (s * a' * s) := congrArg Subtype.val haa
    have h2 : (a' : G)⁻¹ * a = (s * a' * s) * (s * a * s)⁻¹ := by
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * (s * a * s)) * (s * a * s)⁻¹ := by group
        _ = (a' : G)⁻¹ * (a' * (s * a' * s)) * (s * a * s)⁻¹ := by rw [h1]
        _ = (s * a' * s) * (s * a * s)⁻¹ := by group
    have h3 : (a' : G)⁻¹ * a ∈ A ⊓ B := Subgroup.mem_inf.2 ⟨mul_mem (inv_mem a'.2) a.2,
      h2 ▸ mul_mem (hsa a' a'.2) (inv_mem (hsa a a.2))⟩
    rw [hinf, mem_bot] at h3
    apply Subtype.ext
    calc (a : G) = a' * ((a' : G)⁻¹ * a) := by group
      _ = a' := by rw [h3, mul_one]
  have hμsurj : Function.Surjective μ := by
    rintro ⟨p, hpX, hps⟩
    obtain ⟨hcard, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hAB
    have hp' : p ∈ ((A ⊔ B : Subgroup G) : Set G) := hpX
    rw [hset] at hp'
    obtain ⟨a, ha, b, hb, rfl⟩ := hp'
    have hst : s * (a * b) * s = a * b := by
      have := mem_centralizer_singleton_iff.1 hps
      calc s * (a * b) * s = (a * b) * s * s := by rw [this]
        _ = a * b := by rw [mul_assoc, hs, mul_one]
    have h1 : a * b = (s * b * s) * (s * a * s) := by
      calc a * b = s * (a * b) * s := hst.symm
        _ = (s * a * s) * (s * b * s) := by
            rw [show (s * a * s) * (s * b * s) = s * a * (s * s) * b * s by group, hs, mul_one]
            group
        _ = (s * b * s) * (s * a * s) := hAB _ (hsb b hb) _ (hsa a ha) ▸ rfl
    have h2 : (s * b * s)⁻¹ * a = (s * a * s) * b⁻¹ := by
      calc (s * b * s)⁻¹ * a = (s * b * s)⁻¹ * (a * b) * b⁻¹ := by group
        _ = (s * b * s)⁻¹ * ((s * b * s) * (s * a * s)) * b⁻¹ := by rw [h1]
        _ = (s * a * s) * b⁻¹ := by group
    have h3 : (s * b * s)⁻¹ * a ∈ A ⊓ B := Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (hsb b hb)) ha,
      h2 ▸ mul_mem (hsa a ha) (inv_mem hb)⟩
    rw [hinf, mem_bot] at h3
    have ha' : a = s * b * s := by
      calc a = (s * b * s) * ((s * b * s)⁻¹ * a) := by group
        _ = s * b * s := by rw [h3, mul_one]
    have hb' : b = s * a * s := by
      rw [ha', show s * (s * b * s) * s = (s * s) * b * (s * s) by group, hs, one_mul, mul_one]
    refine ⟨⟨a, ha⟩, Subtype.ext ?_⟩
    change a * (s * a * s) = a * b
    rw [← hb']
  exact (HeisLike.congr (MulEquiv.ofBijective μ ⟨hμinj, hμsurj⟩)).2 hP

end Heis

end CFSG.LocalAnalysis.EvenBN.TrialityD4
