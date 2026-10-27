module

public import CFSG.GH74.GLS.NT44.RigidActorClasses
import CFSG.GH74.GLS.Stage1.Thm4.P92Basic
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutNoZ4E4

public section

namespace CFSG.GH74.GLS.NT44

open CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4

theorem exists_z4E4_of_two_mul_card_le {G : Type*} [Group G] [Finite G] {X W B : Subgroup G}
    (hXW : X ⊓ W = ⊥) (hcomm : ∀ a ∈ X ⊔ W, ∀ b ∈ X ⊔ W, a * b = b * a)
    (hX4 : Nat.card X = 4) (hX2 : ∀ a ∈ X, a ^ 2 = 1)
    (eW : W ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
    (hBV : B ≤ X ⊔ W) (hB : Nat.card ↥(X ⊔ W) ≤ 2 * Nat.card B) :
    ∃ a ∈ B, ∃ b ∈ B, ∃ c ∈ B, a ^ 4 = 1 ∧ b ^ 2 = 1 ∧ c ^ 2 = 1 ∧
      a ^ 2 ≠ 1 ∧ b ≠ 1 ∧ b ≠ a ^ 2 ∧ c ≠ 1 ∧ c ≠ a ^ 2 ∧ c ≠ b ∧ c ≠ a ^ 2 * b := by
  classical
  let V : Subgroup G := X ⊔ W
  have hcardW : Nat.card ↥W = 16 := by
    rw [Nat.card_congr eW.toEquiv, Nat.card_prod]
    simp [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hVX : X ≤ V := le_sup_left
  have hVW : W ≤ V := le_sup_right
  have hnorm : W ≤ Subgroup.normalizer (X : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hx
      have hwx : w * h = h * w := hcomm w (hVW hw) h (hVX hx)
      rw [show w * h * w⁻¹ = h by rw [hwx, mul_assoc, mul_inv_cancel, mul_one]]
      exact hx
    · intro hx
      have hxV : w * h * w⁻¹ ∈ V := hVX hx
      have hw'inv : w⁻¹ ∈ V := V.inv_mem (hVW hw)
      have h1 : w⁻¹ * (w * h * w⁻¹) = (w * h * w⁻¹) * w⁻¹ :=
        hcomm w⁻¹ hw'inv _ hxV
      rw [← show w⁻¹ * (w * h * w⁻¹) * w = h by group, h1, mul_assoc,
        inv_mul_cancel, mul_one]
      exact hx
  have hdisj : Disjoint X W := by rw [disjoint_iff, hXW]
  let toSup : X × W → ↥V := fun p =>
    ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hinj : Function.Injective toSup := by
    intro p q h
    exact Subgroup.mul_injective_of_disjoint hdisj (congrArg Subtype.val h)
  have hsurj : Function.Surjective toSup := by
    intro v
    have hv : (v : G) ∈ (↑V : Set G) := v.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left X W hnorm] at hv
    rcases hv with ⟨x, hx, w, hw, hxw⟩
    exact ⟨(⟨x, hx⟩, ⟨w, hw⟩), Subtype.ext hxw⟩
  let e : X × W ≃ ↥V := Equiv.ofBijective toSup ⟨hinj, hsurj⟩
  have hcardV : Nat.card ↥V = 64 := by
    have h := Nat.card_congr e
    rw [Nat.card_prod, hX4, hcardW] at h
    omega
  have hmemV : ∀ v ∈ V, ∃ x ∈ X, ∃ w ∈ W, (x : G) * (w : G) = v := by
    intro v hv
    obtain ⟨p, hp⟩ := hsurj ⟨v, hv⟩
    exact ⟨p.1, p.1.2, p.2, p.2.2, congrArg Subtype.val hp⟩
  have hfour : ∀ z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4), z ^ 4 = 1 := by
    decide
  have hpow4 : ∀ v ∈ V, v ^ 4 = 1 := by
    intro v hv
    obtain ⟨x, hx, w, hw, rfl⟩ := hmemV v hv
    have hx4 : x ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hX2 x hx, one_pow]
    have hw4 : w ^ 4 = 1 := by
      have hwW : (⟨w, hw⟩ : ↥W) ^ 4 = 1 := by
        apply eW.injective
        rw [map_pow, map_one]
        exact hfour (eW ⟨w, hw⟩)
      simpa using congrArg Subtype.val hwW
    have hcw : Commute x w := hcomm x (hVX hx) w (hVW hw)
    rw [hcw.mul_pow 4, hx4, hw4, one_mul]
  let : CommGroup ↥V := CommGroup.mk (fun a b => Subtype.ext (hcomm a a.2 b b.2))
  let ΩV : Subgroup ↥V :=
    { carrier := {u : ↥V | u ^ 2 = 1}
      mul_mem' := by
        intro a b ha hb
        show (a * b) ^ 2 = 1
        rw [mul_pow, ha, hb, one_mul]
      one_mem' := by
        show (1 : ↥V) ^ 2 = 1
        simp
      inv_mem' := by
        intro a ha
        show (a⁻¹) ^ 2 = 1
        rw [inv_pow, ha, inv_one] }
  let Ω : Subgroup G := ΩV.map V.subtype
  have memΩ : ∀ {v : G}, v ∈ V → (v ∈ Ω ↔ v ^ 2 = 1) := by
    intro v hv
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa using congrArg (fun z : ↥V => (z : G)) hu
    · intro hv2
      exact ⟨⟨v, hv⟩, by
        show (⟨v, hv⟩ : ↥V) ^ 2 = 1
        exact Subtype.ext (by simpa using hv2), rfl⟩
  have hTW : Nat.card {w : ↥W // w ^ 2 = 1} = 4 := by
    have hz : Fintype.card
        {z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // z ^ 2 = 1} = 4 := by
      decide
    have hmap : ∀ w : ↥W, w ^ 2 = 1 ↔ (eW w) ^ 2 = 1 := by
      intro w
      constructor
      · intro hw
        rw [← map_pow, hw, map_one]
      · intro hw
        apply eW.injective
        rw [map_pow, map_one]
        exact hw
    have eT : {w : ↥W // w ^ 2 = 1} ≃
        {z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // z ^ 2 = 1} :=
      eW.toEquiv.subtypeEquiv (fun w => hmap w)
    rw [Nat.card_congr eT, Nat.card_eq_fintype_card]
    exact hz
  have hΩVcard : Nat.card ΩV = 16 := by
    change Nat.card {v : ↥V // v ^ 2 = 1} = 16
    have hsub : ∀ v : ↥V, (v ^ 2 = 1) ↔ (((e.symm v).2 : ↥W) ^ 2 = 1) := by
      intro v
      constructor
      · intro hv
        have hp : ((e.symm v).1 : G) * ((e.symm v).2 : G) = (v : G) := by
          have h := congrArg Subtype.val (e.apply_symm_apply v)
          change ((e.symm v).1 : G) * ((e.symm v).2 : G) = (v : G) at h
          exact h
        have hvG : (v : G) ^ 2 = 1 := by
          simpa using congrArg Subtype.val hv
        have hsq : (((e.symm v).2 : G)) ^ 2 = 1 := by
          have hp2 : (((e.symm v).1 : G) * ((e.symm v).2 : G)) ^ 2 = 1 := by
            rw [hp]
            exact hvG
          have hx2 : ((e.symm v).1 : G) ^ 2 = 1 := hX2 _ ((e.symm v).1).2
          have hcw : Commute ((e.symm v).1 : G) ((e.symm v).2 : G) :=
            hcomm _ (hVX ((e.symm v).1).2) _ (hVW ((e.symm v).2).2)
          rw [hcw.mul_pow, hx2, one_mul] at hp2
          exact hp2
        exact Subtype.ext (by simpa using hsq)
      · intro hw
        have hp : ((e.symm v).1 : G) * ((e.symm v).2 : G) = (v : G) := by
          have h := congrArg Subtype.val (e.apply_symm_apply v)
          change ((e.symm v).1 : G) * ((e.symm v).2 : G) = (v : G) at h
          exact h
        have hwG : (((e.symm v).2 : G)) ^ 2 = 1 := by
          simpa using congrArg Subtype.val hw
        have hx2 : ((e.symm v).1 : G) ^ 2 = 1 := hX2 _ ((e.symm v).1).2
        have hcw : Commute ((e.symm v).1 : G) ((e.symm v).2 : G) :=
          hcomm _ (hVX ((e.symm v).1).2) _ (hVW ((e.symm v).2).2)
        have hsq : (((e.symm v).1 : G) * ((e.symm v).2 : G)) ^ 2 = 1 := by
          rw [hcw.mul_pow, hx2, hwG, one_mul]
        exact Subtype.ext (by
          show (v : G) ^ 2 = 1
          rw [← hp]
          exact hsq)
    have hprod : Nat.card {p : X × W // ((p.2 : ↥W) ^ 2 = 1)} =
        Nat.card (X × {w : ↥W // w ^ 2 = 1}) := by
      refine Nat.card_congr ?_
      exact
        { toFun := fun p => (p.1.1, ⟨p.1.2, p.2⟩)
          invFun := fun q => ⟨(q.1, q.2.1), q.2.2⟩
          left_inv := by
            intro p
            rcases p with ⟨⟨x, w⟩, hp⟩
            rfl
          right_inv := by
            intro q
            rcases q with ⟨x, ⟨w, hw⟩⟩
            rfl }
    have h1 : Nat.card {v : ↥V // v ^ 2 = 1} =
        Nat.card {p : X × W // ((p.2 : ↥W) ^ 2 = 1)} :=
      Nat.card_congr (e.symm.subtypeEquiv hsub)
    rw [h1, hprod, Nat.card_prod, hX4, hTW]
  have hΩcard : Nat.card Ω = 16 := by
    rw [show Ω = ΩV.map V.subtype from rfl,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective V), hΩVcard]
  have hBcard : 32 ≤ Nat.card B := by
    have h := hB
    change Nat.card ↥V ≤ 2 * Nat.card B at h
    rw [hcardV] at h
    omega
  have hΩVle : Ω ≤ V := by
    rintro x ⟨u, -, rfl⟩
    exact u.2
  have hD8 : 8 ≤ Nat.card ↥(Ω ⊓ B) := by
    have hΩrel : Ω.relIndex V ≤ 4 := by
      have h := Subgroup.relIndex_mul_card (H := Ω) (K := V)
      rw [inf_eq_left.mpr hΩVle, hΩcard, hcardV] at h
      omega
    have hBrel : B.relIndex V ≤ 2 := by
      have h := Subgroup.relIndex_mul_card (H := B) (K := V)
      rw [inf_eq_left.mpr hBV, hcardV] at h
      by_contra hcon
      push Not at hcon
      have hle : 3 * 32 ≤ B.relIndex V * Nat.card B := Nat.mul_le_mul hcon hBcard
      omega
    have hDrel : (Ω ⊓ B).relIndex V ≤ 8 := by
      have h := Subgroup.relIndex_inf_le (H := Ω) (K := B) (L := V)
      exact h.trans (Nat.mul_le_mul hΩrel hBrel)
    have hinf : (Ω ⊓ B) ⊓ V = Ω ⊓ B := inf_eq_left.mpr (inf_le_left.trans hΩVle)
    have h := Subgroup.relIndex_mul_card (H := Ω ⊓ B) (K := V)
    rw [hinf, hcardV] at h
    by_contra hlt
    push Not at hlt
    have hlt' : Nat.card ↥(Ω ⊓ B) ≤ 7 := by omega
    have hle : (Ω ⊓ B).relIndex V * Nat.card ↥(Ω ⊓ B) ≤ 8 * 7 :=
      Nat.mul_le_mul hDrel hlt'
    omega
  have ha_exists : ∃ a ∈ B, a ^ 2 ≠ 1 := by
    by_contra h
    push Not at h
    have hBΩ : B ≤ Ω := by
      intro x hx
      rw [memΩ (hBV hx)]
      exact h x hx
    have hle : Nat.card B ≤ Nat.card Ω :=
      Nat.card_le_card_of_injective
        (fun x : ↥B => (⟨x.1, hBΩ x.2⟩ : ↥Ω))
        (fun x y hxy => Subtype.ext (congrArg (fun z : ↥Ω => (z : G)) hxy))
    rw [hΩcard] at hle
    omega
  obtain ⟨a, haB, ha2ne⟩ := ha_exists
  have haV : a ∈ V := hBV haB
  have ha4 : a ^ 4 = 1 := hpow4 a haV
  have h4 : (a ^ 2) ^ 2 = a ^ 4 := by rw [← pow_mul]
  have ha2V : a ^ 2 ∈ V := by
    simpa [pow_two] using hBV (B.mul_mem haB haB)
  have ha2Ω : a ^ 2 ∈ Ω := by
    rw [memΩ ha2V, h4, ha4]
  have ha2B : a ^ 2 ∈ B := by
    simpa [pow_two] using B.mul_mem haB haB
  let D : Subgroup G := Ω ⊓ B
  let : Fintype D := Fintype.ofFinite D
  have hD8' : 8 ≤ Nat.card D := by simpa [D] using hD8
  let a2D : D := ⟨a ^ 2, Subgroup.mem_inf.mpr ⟨ha2Ω, ha2B⟩⟩
  have hcardD : (Finset.univ : Finset D).card = Nat.card D := by
    rw [Finset.card_univ, Nat.card_eq_fintype_card]
  have hlt2 : ({1, a2D} : Finset D).card < (Finset.univ : Finset D).card := by
    rw [hcardD]
    have := Finset.card_le_two (a := (1 : D)) (b := a2D)
    omega
  obtain ⟨bD, -, hbDnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt2
  let b : G := bD.1
  have hbB : b ∈ B := (Subgroup.mem_inf.mp bD.2).2
  have hbΩ : b ∈ Ω := (Subgroup.mem_inf.mp bD.2).1
  have hb2 : b ^ 2 = 1 := (memΩ (hBV hbB)).mp hbΩ
  have hb1 : b ≠ 1 := by
    intro h
    apply hbDnot
    rw [Finset.mem_insert, Finset.mem_singleton]
    have hbD1 : bD = 1 :=
      Subtype.ext (p := fun x : G => x ∈ D) (by
        show (bD : G) = ((1 : D) : G)
        exact h)
    exact Or.inl hbD1
  have hb_a2 : b ≠ a ^ 2 := by
    intro h
    apply hbDnot
    rw [Finset.mem_insert, Finset.mem_singleton]
    have hbDa2 : bD = a2D :=
      Subtype.ext (p := fun x : G => x ∈ D) (by
        show (bD : G) = (a2D : G)
        exact h)
    exact Or.inr hbDa2
  let a2bD : D := a2D * bD
  have hlt4 : ({1, a2D, bD, a2bD} : Finset D).card < (Finset.univ : Finset D).card := by
    rw [hcardD]
    have := Finset.card_le_four (a := (1 : D)) (b := a2D) (c := bD) (d := a2bD)
    omega
  obtain ⟨cD, -, hcDnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt4
  let c : G := cD.1
  have hcB : c ∈ B := (Subgroup.mem_inf.mp cD.2).2
  have hcΩ : c ∈ Ω := (Subgroup.mem_inf.mp cD.2).1
  have hc2 : c ^ 2 = 1 := (memΩ (hBV hcB)).mp hcΩ
  have hc1 : c ≠ 1 := by
    intro h
    apply hcDnot
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    have hcD1 : cD = 1 :=
      Subtype.ext (p := fun x : G => x ∈ D) (by
        show (cD : G) = ((1 : D) : G)
        exact h)
    exact Or.inl hcD1
  have hc_a2 : c ≠ a ^ 2 := by
    intro h
    apply hcDnot
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    have hcDa2 : cD = a2D :=
      Subtype.ext (p := fun x : G => x ∈ D) (by
        show (cD : G) = (a2D : G)
        exact h)
    exact Or.inr (Or.inl hcDa2)
  have hc_b : c ≠ b := by
    intro h
    apply hcDnot
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    have hcDb : cD = bD :=
      Subtype.ext (p := fun x : G => x ∈ D) (by
        show (cD : G) = (bD : G)
        exact h)
    exact Or.inr (Or.inr (Or.inl hcDb))
  have hc_a2b : c ≠ a ^ 2 * b := by
    intro h
    apply hcDnot
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    have hcDa2b : cD = a2bD :=
      Subtype.ext (p := fun x : G => x ∈ D) (by
        show (cD : G) = (a2bD : G)
        exact h)
    exact Or.inr (Or.inr (Or.inr hcDa2b))
  exact ⟨a, haB, b, hbB, c, hcB, ha4, hb2, hc2, ha2ne, hb1, hb_a2, hc1, hc_a2,
    hc_b, hc_a2b⟩

theorem card_le_sixteen_of_mem_rigidSet
    {G : Type} [Group G] [Finite G] {fullQ : Type} [Group fullQ]
    (hL34 : IsL34Quotient fullQ) (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {t : G} {L : Subgroup G} (hL : L ∈ RigidSet fullQ t) {A : Subgroup (MulAut (kBar L))}
    (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hs : ∀ a ∈ A, a * a = 1) :
    Nat.card A ≤ 16 := by
  classical
  obtain ⟨β⟩ := nonempty_centerQuotient_equiv_of_mem_rigidSet hL34 h16 hL
  have hperf : Group.IsPerfect (kBar L) := (TwoThin.isQuasisimple_hat (P92.rig_pcomp hL)).1
  obtain ⟨e, -, -⟩ := CFSG.ComponentClassification.PSL3Four.full_automorphism_action
  let φ : MulAut (kBar L) →* Equiv.Perm (Fin 42) :=
    CFSG.ComponentClassification.PSL3Four.R.subtype.comp
      (e.symm.toMonoidHom.comp
        ((MulAut.congr β).toMonoidHom.comp
          (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom (kBar L))))
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have h1 : e.symm ((MulAut.congr β)
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom (kBar L) x)) =
        e.symm ((MulAut.congr β)
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom (kBar L) y)) :=
      Subgroup.subtype_injective CFSG.ComponentClassification.PSL3Four.R hxy
    have h2 := e.symm.injective h1
    have h3 := (MulAut.congr β).injective h2
    exact CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective (kBar L) h3
  have hAR : A.map φ ≤ CFSG.ComponentClassification.PSL3Four.R := by
    rintro x ⟨a, -, rfl⟩
    exact (e.symm ((MulAut.congr β)
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom (kBar L) a))).2
  have hAc : ∀ x ∈ A.map φ, ∀ y ∈ A.map φ, x * y = y * x := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc a ha b hb]
  have hAs : ∀ x ∈ A.map φ, x * x = 1 := by
    rintro x ⟨a, ha, rfl⟩
    rw [← map_mul, hs a ha, map_one]
  have hcard := CFSG.ComponentClassification.HSFLit.AutL34.card_le_sixteen hAR hAc hAs
  rwa [Subgroup.card_map_of_injective hφinj] at hcard

theorem mulAut_noZ4E4_of_mem_rigidSet
    {G : Type} [Group G] [Finite G] {fullQ : Type} [Group fullQ]
    (hL34 : IsL34Quotient fullQ) (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {t : G} {L : Subgroup G} (hL : L ∈ RigidSet fullQ t) {a b c : MulAut (kBar L)}
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (ha4 : a ^ 4 = 1) (hb2 : b ^ 2 = 1) (hc2 : c ^ 2 = 1) :
    a ^ 2 = 1 ∨ b = 1 ∨ b = a ^ 2 ∨ c = 1 ∨ c = a ^ 2 ∨ c = b ∨ c = a ^ 2 * b := by
  classical
  obtain ⟨β⟩ := nonempty_centerQuotient_equiv_of_mem_rigidSet hL34 h16 hL
  have hperf : Group.IsPerfect (kBar L) := (TwoThin.isQuasisimple_hat (P92.rig_pcomp hL)).1
  let ψ : MulAut (kBar L) →*
      MulAut (kBar L ⧸ Subgroup.center (kBar L)) :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom (kBar L)
  have hψ : Function.Injective ψ :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective (kBar L)
  have hab' : ψ a * ψ b = ψ b * ψ a := by rw [← map_mul, ← map_mul, hab]
  have hac' : ψ a * ψ c = ψ c * ψ a := by rw [← map_mul, ← map_mul, hac]
  have hbc' : ψ b * ψ c = ψ c * ψ b := by rw [← map_mul, ← map_mul, hbc]
  have ha4' : (ψ a) ^ 4 = 1 := by rw [← map_pow, ha4, map_one]
  have hb2' : (ψ b) ^ 2 = 1 := by rw [← map_pow, hb2, map_one]
  have hc2' : (ψ c) ^ 2 = 1 := by rw [← map_pow, hc2, map_one]
  have h := CFSG.ComponentClassification.PSL3Four.mulAut_noZ4E4 β
    (a := ψ a) (b := ψ b) (c := ψ c) hab' hac' hbc' ha4' hb2' hc2'
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl (hψ (by rw [map_pow, map_one]; exact h))
  · exact Or.inr (Or.inl (hψ (by rw [h, map_one])))
  · exact Or.inr (Or.inr (Or.inl (hψ (by rw [h, map_pow]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hψ (by rw [h, map_one])))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hψ (by rw [h, map_pow]))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hψ h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (hψ (by rw [h, ← map_pow, ← map_mul])))))))

end CFSG.GH74.GLS.NT44
