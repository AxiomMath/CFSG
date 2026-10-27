module

public import Mathlib.GroupTheory.Goursat
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Tactic.Group

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Proving

open scoped commutatorElement

theorem goursat_simple_subdirect {S T : Type*} [Group S] [Group T]
    [IsSimpleGroup S] [IsSimpleGroup T]
    (hnot : ¬ Nonempty (S ≃* T)) (I : Subgroup (S × T))
    (h1 : Function.Surjective (Prod.fst ∘ I.subtype))
    (h2 : Function.Surjective (Prod.snd ∘ I.subtype)) : I = ⊤ := by
  obtain ⟨e, -⟩ := Subgroup.goursat_surjective h1 h2
  have := Subgroup.normal_goursatFst h1
  have := Subgroup.normal_goursatSnd h2
  rcases Subgroup.Normal.eq_bot_or_eq_top I.goursatFst with hf | hf <;>
    rcases Subgroup.Normal.eq_bot_or_eq_top I.goursatSnd with hs | hs
  · exfalso
    exact hnot ⟨((QuotientGroup.quotientMulEquivOfEq hf).trans QuotientGroup.quotientBot).symm.trans
      (e.trans ((QuotientGroup.quotientMulEquivOfEq hs).trans QuotientGroup.quotientBot))⟩
  ·
    exfalso
    have h1 : Subsingleton (T ⧸ I.goursatSnd) := by rw [hs]; exact QuotientGroup.subsingleton_quotient_top
    have h2 : Subsingleton (S ⧸ I.goursatFst) := e.symm.surjective.subsingleton
    rw [hf] at h2
    have : Subsingleton S := (QuotientGroup.quotientBot (G := S)).symm.injective.subsingleton
    exact not_subsingleton S inferInstance
  ·
    exfalso
    have h1 : Subsingleton (S ⧸ I.goursatFst) := by rw [hf]; exact QuotientGroup.subsingleton_quotient_top
    have h2 : Subsingleton (T ⧸ I.goursatSnd) := e.surjective.subsingleton
    rw [hs] at h2
    have : Subsingleton T := (QuotientGroup.quotientBot (G := T)).symm.injective.subsingleton
    exact not_subsingleton T inferInstance
  · ext ⟨s, t⟩
    simp only [Subgroup.mem_top, iff_true]
    have hs1 : (s, (1 : T)) ∈ I := by
      have : s ∈ I.goursatFst := by rw [hf]; exact Subgroup.mem_top s
      exact Subgroup.mem_goursatFst.mp this
    have ht1 : ((1 : S), t) ∈ I := by
      have : t ∈ I.goursatSnd := by rw [hs]; exact Subgroup.mem_top t
      exact Subgroup.mem_goursatSnd.mp this
    have := I.mul_mem hs1 ht1
    simpa using this

theorem commutatorElement_mul_left_of_comm {G : Type*} [Group G] {z g : G}
    (hzg : z * g = g * z) (a : G) :
    ⁅a * z, g⁆ = ⁅a, g⁆ := by
  have e : ⁅a * z, g⁆ = a * (z * g * z⁻¹) * a⁻¹ * g⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e, hzg, commutatorElement_def]; group

theorem commutatorElement_mul_right_of_comm {G : Type*} [Group G] {w x y : G}
    (hwx : w * x = x * w) : ⁅x, y * w⁆ = ⁅x, y⁆ := by
  have hc : Commute w x := hwx
  have hinv : w * x⁻¹ * w⁻¹ = x⁻¹ := by
    rw [hc.inv_right.eq, mul_assoc, mul_inv_cancel, mul_one]
  have e : ⁅x, y * w⁆ = x * y * (w * x⁻¹ * w⁻¹) * y⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e, hinv, commutatorElement_def]

theorem commutator_le_of_decomp {G : Type*} [Group G] (M X : Subgroup G) (Z : Set G)
    (hXM : X ≤ M) (hZ : ∀ z ∈ Z, ∀ m ∈ M, z * m = m * z)
    (hM : ∀ g ∈ M, ∃ x ∈ X, ∃ z ∈ Z, g = x * z) :
    ⁅M, M⁆ ≤ X := by
  rw [Subgroup.commutator_def, Subgroup.closure_le]
  rintro _ ⟨a, ha, b, hb, rfl⟩
  obtain ⟨x, hx, z, hz, rfl⟩ := hM a ha
  obtain ⟨y, hy, w, hw, rfl⟩ := hM b hb
  have hxM : x ∈ M := hXM hx
  have hwx : w * x = x * w := hZ w hw x hxM
  rw [commutatorElement_mul_left_of_comm (hZ z hz (y * w) hb) x,
    commutatorElement_mul_right_of_comm hwx, commutatorElement_def]
  exact X.mul_mem (X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)) (X.inv_mem hy)

theorem mem_sup_eq_mul_of_comm {G : Type*} [Group G] (A B : Subgroup G)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ g ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  let T : Subgroup G :=
    { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
        have h : a₂ * b₁ = b₁ * a₂ := hcomm a₂ ha₂ b₁ hb₁
        calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
          _ = a₁ * (a₂ * b₁) * b₂ := by rw [← h]
          _ = a₁ * a₂ * (b₁ * b₂) := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have h : a * b = b * a := hcomm a ha b hb
        calc (a * b)⁻¹ = (b * a)⁻¹ := by rw [h]
          _ = a⁻¹ * b⁻¹ := by group }
  have hT : A ⊔ B ≤ T :=
    sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
      (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  intro g hg
  exact hT hg

theorem conj_mem_of_mem_sup {G : Type*} [Group G] (A B : Subgroup G)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ m ∈ A ⊔ B, ∀ b ∈ B, m * b * m⁻¹ ∈ B := by
  intro m hm b hb
  obtain ⟨a, ha, b', hb', rfl⟩ := mem_sup_eq_mul_of_comm A B hcomm m hm
  have hd : b' * b * b'⁻¹ ∈ B := B.mul_mem (B.mul_mem hb' hb) (B.inv_mem hb')
  have hc : a * (b' * b * b'⁻¹) = (b' * b * b'⁻¹) * a := hcomm a ha _ hd
  have e : a * b' * b * (a * b')⁻¹ = b' * b * b'⁻¹ := by
    calc a * b' * b * (a * b')⁻¹ = a * (b' * b * b'⁻¹) * a⁻¹ := by group
      _ = (b' * b * b'⁻¹) * a * a⁻¹ := by rw [hc]
      _ = b' * b * b'⁻¹ := by group
  rw [e]
  exact hd

theorem mem_sup_eq_mul_right {G : Type*} [Group G] (A B X : Subgroup G)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hXle : X ≤ A ⊔ B) :
    ∀ g ∈ X ⊔ B, ∃ x ∈ X, ∃ b ∈ B, g = x * b := by
  let T : Subgroup G :=
    { carrier := {g | ∃ x ∈ X, ∃ b ∈ B, g = x * b}
      mul_mem' := by
        rintro _ _ ⟨x₁, hx₁, b₁, hb₁, rfl⟩ ⟨x₂, hx₂, b₂, hb₂, rfl⟩
        have hc : x₂⁻¹ * b₁ * x₂ ∈ B := by
          have := conj_mem_of_mem_sup A B hcomm x₂⁻¹ ((A ⊔ B).inv_mem (hXle hx₂)) b₁ hb₁
          rwa [inv_inv] at this
        refine ⟨x₁ * x₂, X.mul_mem hx₁ hx₂, x₂⁻¹ * b₁ * x₂ * b₂, B.mul_mem hc hb₂, ?_⟩
        group
      one_mem' := ⟨1, X.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨x, hx, b, hb, rfl⟩
        have hc : x * b⁻¹ * x⁻¹ ∈ B := conj_mem_of_mem_sup A B hcomm x (hXle hx) b⁻¹ (B.inv_mem hb)
        exact ⟨x⁻¹, X.inv_mem hx, x * b⁻¹ * x⁻¹, hc, by group⟩ }
  have hT : X ⊔ B ≤ T :=
    sup_le (fun x hx => ⟨x, hx, 1, B.one_mem, by simp⟩)
      (fun b hb => ⟨1, X.one_mem, b, hb, by simp⟩)
  intro g hg
  exact hT hg

theorem decomp_mod_center {G : Type*} [Group G] (A B X : Subgroup G)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAs : IsSimpleGroup (↥A ⧸ Subgroup.center ↥A))
    (hBs : IsSimpleGroup (↥B ⧸ Subgroup.center ↥B))
    (hnot : ¬ Nonempty ((↥A ⧸ Subgroup.center ↥A) ≃* (↥B ⧸ Subgroup.center ↥B)))
    (hXA : X ⊔ A = A ⊔ B) (hXB : X ⊔ B = A ⊔ B) (hXle : X ≤ A ⊔ B) :
    ∀ g ∈ A ⊔ B, ∃ x ∈ X, ∃ z1 : A, z1 ∈ Subgroup.center ↥A ∧
      ∃ z2 : B, z2 ∈ Subgroup.center ↥B ∧ g = x * ((z1 : G) * (z2 : G)) := by
  have := hAs
  have := hBs
  have hc : ∀ m : A, ∀ n : B, Commute (m : G) (n : G) := fun m n => hcomm _ m.2 _ n.2
  let ps : A × B →* G := MonoidHom.noncommCoprod A.subtype B.subtype hc
  have hps : ∀ p : A × B, ps p = (p.1 : G) * (p.2 : G) := fun p => rfl
  have hcomm' : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b := fun b hb a ha => (hcomm a ha b hb).symm
  have hXle' : X ≤ B ⊔ A := hXle.trans (le_of_eq (sup_comm A B))
  let I : Subgroup (A × B) := X.comap ps
  let pq : A × B →* (↥A ⧸ Subgroup.center ↥A) × (↥B ⧸ Subgroup.center ↥B) :=
    (QuotientGroup.mk' (Subgroup.center ↥A)).prodMap (QuotientGroup.mk' (Subgroup.center ↥B))
  let J : Subgroup ((↥A ⧸ Subgroup.center ↥A) × (↥B ⧸ Subgroup.center ↥B)) := I.map pq
  have h1 : Function.Surjective (Prod.fst ∘ J.subtype) := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    have hmem : (a : G) ∈ X ⊔ B := by rw [hXB]; exact Subgroup.mem_sup_left a.2
    obtain ⟨x0, hx0, b0, hb0, hab⟩ := mem_sup_eq_mul_right A B X hcomm hXle _ hmem
    have hp : ((a, ⟨b0⁻¹, B.inv_mem hb0⟩) : A × B) ∈ I := by
      show ps _ ∈ X
      have e : (a : G) * b0⁻¹ = x0 := by rw [hab]; group
      show (a : G) * (b0⁻¹ : G) ∈ X
      rw [e]; exact hx0
    exact ⟨⟨pq (a, ⟨b0⁻¹, B.inv_mem hb0⟩), Subgroup.mem_map_of_mem pq hp⟩, rfl⟩
  have h2 : Function.Surjective (Prod.snd ∘ J.subtype) := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    have hmem : (b : G) ∈ X ⊔ A := by rw [hXA]; exact Subgroup.mem_sup_right b.2
    obtain ⟨x0, hx0, a0, ha0, hba⟩ := mem_sup_eq_mul_right B A X hcomm' hXle' _ hmem
    have hp : ((⟨a0⁻¹, A.inv_mem ha0⟩, b) : A × B) ∈ I := by
      show ps _ ∈ X
      have e1 : a0⁻¹ * (b : G) = (b : G) * a0⁻¹ := hcomm a0⁻¹ (A.inv_mem ha0) b b.2
      have e2 : (b : G) * a0⁻¹ = x0 := by rw [hba]; group
      show a0⁻¹ * (b : G) ∈ X
      rw [e1, e2]; exact hx0
    exact ⟨⟨pq (⟨a0⁻¹, A.inv_mem ha0⟩, b), Subgroup.mem_map_of_mem pq hp⟩, rfl⟩
  have hJ : J = ⊤ := goursat_simple_subdirect hnot J h1 h2
  intro g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_eq_mul_of_comm A B hcomm g hg
  let q : A × B := (⟨a, ha⟩, ⟨b, hb⟩)
  have hqJ : pq q ∈ J := by rw [hJ]; exact Subgroup.mem_top _
  obtain ⟨i, hi, hpi⟩ := Subgroup.mem_map.mp hqJ
  have hz : pq (i⁻¹ * q) = 1 := by rw [map_mul, map_inv, hpi, inv_mul_cancel]
  have hz1 : QuotientGroup.mk' (Subgroup.center ↥A) (i⁻¹ * q).1 = 1 := congrArg Prod.fst hz
  have hz2 : QuotientGroup.mk' (Subgroup.center ↥B) (i⁻¹ * q).2 = 1 := congrArg Prod.snd hz
  have key : ps q = ps i * ps (i⁻¹ * q) := by rw [← map_mul, mul_inv_cancel_left]
  refine ⟨ps i, hi, (i⁻¹ * q).1, (QuotientGroup.eq_one_iff _).mp hz1,
    (i⁻¹ * q).2, (QuotientGroup.eq_one_iff _).mp hz2, ?_⟩
  calc a * b = ps q := rfl
    _ = ps i * ps (i⁻¹ * q) := key
    _ = ps i * (((i⁻¹ * q).1 : G) * ((i⁻¹ * q).2 : G)) := by rw [hps (i⁻¹ * q)]

abbrev centralProd {G : Type*} [Group G] (A B : Subgroup G) : Set G :=
  {z | ∃ z1 : A, z1 ∈ Subgroup.center ↥A ∧ ∃ z2 : B, z2 ∈ Subgroup.center ↥B ∧ z = (z1 : G) * (z2 : G)}

theorem comm_mul_mul {G : Type*} [Group G] {z a b : G} (ha : z * a = a * z)
    (hb : z * b = b * z) : z * (a * b) = (a * b) * z := by
  rw [← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]

theorem goursat_commute_perfect {G : Type*} [Group G] (A B X : Subgroup G)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAs : IsSimpleGroup (↥A ⧸ Subgroup.center ↥A))
    (hBs : IsSimpleGroup (↥B ⧸ Subgroup.center ↥B))
    (hnot : ¬ Nonempty ((↥A ⧸ Subgroup.center ↥A) ≃* (↥B ⧸ Subgroup.center ↥B)))
    (hXA : X ⊔ A = A ⊔ B) (hXB : X ⊔ B = A ⊔ B) (hXle : X ≤ A ⊔ B) :
    ⁅A ⊔ B, A ⊔ B⁆ ≤ X := by
  refine commutator_le_of_decomp (A ⊔ B) X (centralProd A B) hXle ?_ ?_
  · rintro z ⟨z1, hz1, z2, hz2, rfl⟩ m hm
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_eq_mul_of_comm A B hcomm m hm
    have hza : a * (z1 : G) = (z1 : G) * a :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hz1 ⟨a, ha⟩)
    have hzb : b * (z2 : G) = (z2 : G) * b :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hz2 ⟨b, hb⟩)
    have hu_a : (z1 : G) * a = a * (z1 : G) := hza.symm
    have hu_b : (z1 : G) * b = b * (z1 : G) := hcomm (z1 : G) z1.2 b hb
    have hv_a : (z2 : G) * a = a * (z2 : G) := (hcomm a ha (z2 : G) z2.2).symm
    have hv_b : (z2 : G) * b = b * (z2 : G) := hzb.symm
    have hu_m := comm_mul_mul hu_a hu_b
    have hv_m := comm_mul_mul hv_a hv_b
    calc ((z1 : G) * (z2 : G)) * (a * b) = (z1 : G) * ((z2 : G) * (a * b)) := mul_assoc _ _ _
      _ = (z1 : G) * ((a * b) * (z2 : G)) := by rw [hv_m]
      _ = ((z1 : G) * (a * b)) * (z2 : G) := (mul_assoc _ _ _).symm
      _ = ((a * b) * (z1 : G)) * (z2 : G) := by rw [hu_m]
      _ = (a * b) * ((z1 : G) * (z2 : G)) := mul_assoc _ _ _
  · intro g hg
    obtain ⟨x, hx, z1, hz1, z2, hz2, hgx⟩ :=
      decomp_mod_center A B X hcomm hAs hBs hnot hXA hXB hXle g hg
    exact ⟨x, hx, (z1 : G) * (z2 : G), ⟨z1, hz1, z2, hz2, rfl⟩, hgx⟩

theorem goursat_eq_sup_of_perfect {G : Type*} [Group G] (A B X : Subgroup G)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAs : IsSimpleGroup (↥A ⧸ Subgroup.center ↥A))
    (hBs : IsSimpleGroup (↥B ⧸ Subgroup.center ↥B))
    (hnot : ¬ Nonempty ((↥A ⧸ Subgroup.center ↥A) ≃* (↥B ⧸ Subgroup.center ↥B)))
    (hXA : X ⊔ A = A ⊔ B) (hXB : X ⊔ B = A ⊔ B) (hXle : X ≤ A ⊔ B)
    (hA : ⁅A, A⁆ = A) (hB : ⁅B, B⁆ = B) : X = A ⊔ B := by
  refine le_antisymm hXle ?_
  have hM : A ⊔ B ≤ ⁅A ⊔ B, A ⊔ B⁆ := by
    refine sup_le ?_ ?_
    · calc A = ⁅A, A⁆ := hA.symm
        _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
    · calc B = ⁅B, B⁆ := hB.symm
        _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_right le_sup_right
  exact hM.trans (goursat_commute_perfect A B X hcomm hAs hBs hnot hXA hXB hXle)

end CFSG.HardMathSupport.Seitz.TrialityOdd.Proving
